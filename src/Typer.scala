package Assign3.Typer

import Assign3.Syntax.Syntax._
import scala.collection.immutable.ListMap

object Typer {
  // ======================================================================
  // Part 1: Typechecking
  // ======================================================================

  val generator = SymGenerator()

  def isBaseType(ty: Type): Boolean = ty match {
    case TyBool | TyInt | TyString | TyUnit => true
    case _                                  => false
  }

  def isEqType(ty: Type): Boolean = ty match {
    case TyUnit | TyInt | TyString | TyBool => true
    case TyVariant(tys)   => tys.forall((l, ty0) => isEqType(ty0))
    case TyPair(ty1, ty2) => isEqType(ty1) && isEqType(ty2)
    case _                => false
  }
  ////////////////////
  // EXERCISE 2     //
  ////////////////////
  def subtype(ty1: Type, ty2: Type): Boolean = (ty1, ty2) match {

    // base types, check if they are the same
    case (ty1, ty2) if ty1 == ty2 && isBaseType(ty1) => true

    // pair type, check if the right side is a subtype of the left side
    case (TyPair(ty1, ty2), TyPair(ty_p1, ty_p2)) =>
      subtype(ty1, ty_p1) && subtype(ty2, ty_p2)

    // function type, check if the right side is a subtype of the left side
    case (TyFun(ty1, ty2), TyFun(ty_p1, ty_p2)) =>
      subtype(ty2, ty_p2) && subtype(ty_p1, ty1)

    // variant type, check if the right side is a subtype of the left side
    case (TyVariant(tys1), TyVariant(tys2)) =>
      if (tys1.size > tys2.size) {
        return false
      }
      tys1.forall { case (label, ty1) =>
        tys2.get(label) match {
          case Some(ty2) => subtype(ty1, ty2)
          case None      => false
        }
      }

    // record type, check if the right side is a subtype of the left side
    case (TyRecord(tys1), TyRecord(tys2)) => {
      if (tys1.size < tys2.size) {
        return false
      }
      // checking every elem on right is subtype of left
      tys2.forall((l, ty) => {
        tys1.get(l) match {
          case Some(ty1) => subtype(ty1, ty)
          case None      => false
        }
      })
    }

    // check that the right side is a subtype of the left side
    case (TyBag(ty1), TyBag(ty2)) => subtype(ty1, ty2)

    // default case
    case _ => false

  }

  ////////////////////
  // EXERCISE 3     //
  ////////////////////
  // checking mode
  def tyCheck(ctx: Env, e: Expr, ty: Type): Unit = (e, ty) match {

    // if then else
    case (IfThenElse(e_cond, e1, e2), ty) =>
      // check condition type checks to be a boolean
      tyCheck(ctx, e_cond, TyBool)
      // check both branches have the same type
      tyCheck(ctx, e1, ty)
      tyCheck(ctx, e2, ty)

    // let binding
    case (Let(x, e1, e2), ty) =>
      val x_ty = tyInfer(ctx, e1)
      val new_ctx = ctx + (x -> x_ty)
      tyCheck(new_ctx, e2, ty)

    // lambda expression
    case (Lambda(x, e), TyFun(ty1, ty2)) =>
      // assume arg x has type ty1
      var new_ctx = ctx + (x -> ty1)
      // check body has type ty2
      tyCheck(new_ctx, e, ty2)

    // recursive function
    case (Rec(f, x, e_body), TyFun(ty1, ty2)) =>
      // assume f is of type ty1 -> ty2 and x is of type ty1
      var new_ctx = ctx + (f -> TyFun(ty1, ty2)) + (x -> ty1)
      // check body has type ty2
      tyCheck(new_ctx, e_body, ty2)

    // pairs
    case (Pair(e1, e2), TyPair(ty1, ty2)) =>
      tyCheck(ctx, e1, ty1)
      tyCheck(ctx, e2, ty2)

    // record
    case (Record(es), TyRecord(tys)) =>
      // check that tys is a subset of es and infer additional types
      tys.foreach((l, ty) => {
        es.get(l) match {
          case Some(e) => tyCheck(ctx, e, ty)
          case None    => sys.error("tyCheck: record missing field " ++ l)
        }
      })
      // if we reach here we have checked all fields, and now we need to infer the rest
      es.foreach((l, e) => {
        tys.get(l) match {
          case Some(ty) => ()
          case None     => tyInfer(ctx, e)
        }
      })

    // projection
    case (Proj(e, l), ty) =>
      tyCheck(ctx, e, TyRecord(ListMap(l -> ty)))

    // select for variant
    case (Variant(l, e), TyVariant(tys)) =>
      tys.get(l) match {
        case Some(ty0) => tyCheck(ctx, e, ty0)
        case None => sys.error(s"tyCheck: missing field $l in variant type")
      }

    // case split
    case (Case(e, cases), ty) =>
      val tyVar = tyInfer(ctx, e)
      tyVar match {
        case TyVariant(tys) =>
          // check all cases, and make sure they are all the same type if they exist in the variant
          cases.foreach { case (l, (x, e0)) =>
            tys.get(l) match {
              case Some(ty0) =>
                val newCtx = ctx + (x -> ty0)
                tyCheck(newCtx, e0, ty)
              case None =>
                sys.error(s"tyCheck: not exhaustive case for variant type")
            }
          }
        case _ =>
          sys.error("tyCheck: expected a variant type for case expression")
      }

    // bag
    case (Bag(elems), TyBag(ty)) =>
      elems.foreach(e => tyCheck(ctx, e, ty))

    // flat map on bag
    case (FlatMap(e1, e2), TyBag(ty2)) =>
      // we should get bag of ty1
      val e1_type = tyInfer(ctx, e1)
      e1_type match {
        case TyBag(ty1) => tyCheck(ctx, e2, TyFun(ty1, TyBag(ty2)))
        case _          => sys.error("tyCheck: expected bag type")
      }

    // when function on bag
    case (When(e1, e2), TyBag(ty)) =>
      tyCheck(ctx, e1, TyBool)
      tyCheck(ctx, e2, TyBag(ty))

    // sum on bag
    case (Sum(e1, e2), TyBag(ty)) =>
      tyCheck(ctx, e1, TyBag(ty))
      tyCheck(ctx, e2, TyBag(ty))

    // diff on bag
    case (Diff(e1, e2), TyBag(ty)) =>
      if (!isEqType(ty)) {
        sys.error("tyCheck: cannot diff on type " ++ ty.toString)
      }
      tyCheck(ctx, e1, TyBag(ty))
      tyCheck(ctx, e2, TyBag(ty))

    // comprehension base case
    case (Comprehension(e, Nil), TyBag(ty)) =>
      tyCheck(ctx, e, ty)

    // comprehension with bind
    case (Comprehension(e, Bind(x, ei) :: es), TyBag(ty)) =>
      // infer type of ei to be bag
      val elemType = tyInfer(ctx, ei)
      elemType match {
        case TyBag(tyPrime) =>
          val new_ctx = ctx + (x -> tyPrime)
          tyCheck(new_ctx, Comprehension(e, es), TyBag(ty))
        case _ => sys.error("tyInfer: expected bag type")
      }

    // comprehension with let
    case (Comprehension(e, CLet(x, ei) :: es), TyBag(ty)) =>
      val elemType = tyInfer(ctx, ei)
      val new_ctx = ctx + (x -> elemType)
      tyCheck(new_ctx, Comprehension(e, es), TyBag(ty))

    // comprehension with guard
    case (Comprehension(e, Guard(ei) :: es), TyBag(ty)) =>
      tyCheck(ctx, ei, TyBool)
      tyCheck(ctx, Comprehension(e, es), TyBag(ty))

    // let function
    case (LetFun(f, func_type, x, e1, e2), ty) =>
      func_type match {
        case TyFun(ty1, ty2) => {
          val new_ctx_1 = ctx + (x -> ty1)
          tyCheck(new_ctx_1, e1, ty2)
          val new_ctx_2 = ctx + (f -> func_type)
          tyCheck(new_ctx_2, e2, ty)
        }
        case _ => sys.error("tyCheck: expected function type")
      }

    // let recursive
    case (LetRec(f, func_type, x, e1, e2), ty) =>
      func_type match {
        case TyFun(ty1, ty2) => {
          val new_ctx_1 = ctx + (f -> func_type) + (x -> ty1)
          val new_ctx_2 = ctx + (f -> func_type)
          tyCheck(new_ctx_1, e1, ty2)
          tyCheck(new_ctx_2, e2, ty)
        }
        case _ => sys.error("tyCheck: expected function type")
      }

    // let pair
    case (LetPair(x, y, e1, e2), ty) =>
      var e1_ty = tyInfer(ctx, e1)
      e1_ty match
        case TyPair(ty1, ty2) =>
          val new_ctx = ctx + (x -> ty1) + (y -> ty2)
          tyCheck(new_ctx, e2, ty)

        case _ => sys.error("tyCheck: expected pair type")

    // let record
    case (LetRecord(xs, e1, e2), ty) =>
      // infer e1_type
      val e1_type = tyInfer(ctx, e1)
      e1_type match {
        case TyRecord(tys) =>
          // add each field to the context
          val new_ctx = xs.foldLeft(ctx) { case (curr, (l, x)) =>
            tys.get(l) match {
              case Some(ty) => curr + (x -> ty)
              case None => sys.error("tyCheck: did not find field in record")
            }
          }
          tyCheck(new_ctx, e2, ty)
        case _ => sys.error("tyCheck: expected record type")
      }

    // default case
    case (e1, ty_prime) =>
      val ty = tyInfer(ctx, e1)
      if (!subtype(ty, ty_prime)) {
        sys.error(
          "tyCheck: expected type " ++ ty_prime.toString ++ " but got " ++ ty.toString
        )
      }
  }

  // inference mode
  def tyInfer(ctx: Env, e: Expr): Type = e match {
    // value
    case v: Value =>
      sys.error("tyCheck: values should not appear at this stage")

    // unit type
    case Unit => (TyUnit)

    // arithmetic
    case Num(_) => (TyInt)
    case Plus(e1, e2) =>
      tyCheck(ctx, e1, TyInt)
      tyCheck(ctx, e2, TyInt)
      (TyInt)
    case Minus(e1, e2) =>
      tyCheck(ctx, e1, TyInt)
      tyCheck(ctx, e2, TyInt)
      (TyInt)
    case Times(e1, e2) =>
      tyCheck(ctx, e1, TyInt)
      tyCheck(ctx, e2, TyInt)
      (TyInt)

    // booleans
    case Bool(_) => (TyBool)
    case Eq(e1, e2) =>
      val ty = tyInfer(ctx, e1)
      if (!isEqType(ty)) {
        sys.error("tyCheck: cannot test equality of type " ++ ty.toString)
      }
      tyCheck(ctx, e2, ty)
      (TyBool)
    case Less(e1, e2) =>
      tyCheck(ctx, e1, TyInt)
      tyCheck(ctx, e2, TyInt)
      (TyBool)
    case IfThenElse(e, e1, e2) =>
      tyCheck(ctx, e, TyBool)
      val ty = tyInfer(ctx, e1)
      tyCheck(ctx, e2, ty)
      (ty)

    // Strings
    case Str(_) => (TyString)
    case Length(e) =>
      tyCheck(ctx, e, TyString)
      (TyInt)
    case Index(e1, e2) =>
      tyCheck(ctx, e1, TyString)
      tyCheck(ctx, e2, TyInt)
      (TyString)
    case Concat(e1, e2) =>
      tyCheck(ctx, e1, TyString)
      tyCheck(ctx, e2, TyString)
      (TyString)

    // Variables and Annotations
    case Var(x) =>
      ctx.get(x) match {
        case Some(ty) => ty
        case None     => sys.error("tyInfer: variable not found (isn't bound)")
      }
    case Anno(e, ty) =>
      tyCheck(ctx, e, ty)
      ty

    // Let binding
    case Let(x, e1, e2) =>
      val ty1 = tyInfer(ctx, e1)
      val new_ctx = ctx + (x -> ty1)
      tyInfer(new_ctx, e2)

    // Functions
    case Apply(e1, e2) =>
      val ty1 = tyInfer(ctx, e1)
      ty1 match {
        case TyFun(ty_arg, ty_res) =>
          tyCheck(ctx, e2, ty_arg)
          ty_res
        case _ => sys.error("tyInfer: expected function type")
      }

    // Records
    case Record(es) =>
      val types_in_record = es.map { case (l, e) => (l, tyInfer(ctx, e)) }
      TyRecord(types_in_record)

    case Proj(e1, l) =>
      // infer e type, should be record
      val e1_ty = tyInfer(ctx, e1)
      e1_ty match {
        case TyRecord(tys) =>
          tys.get(l) match {
            case Some(ty) => ty
            case None     => sys.error("tyInfer: field not found in record")
          }
        case _ => sys.error("tyInfer: expected record type")
      }

    // Variants
    case Variant(l, e_var) =>
      TyVariant(ListMap(l -> tyInfer(ctx, e_var)))

    // Pairing
    case Pair(e1, e2) =>
      val ty1 = tyInfer(ctx, e1)
      val ty2 = tyInfer(ctx, e2)
      TyPair(ty1, ty2)
    case First(e) =>
      tyInfer(ctx, e) match {
        case TyPair(ty1, _) => ty1
        case _              => sys.error("tyInfer: expected pair type")
      }
    case Second(e) =>
      tyInfer(ctx, e) match {
        case TyPair(_, ty2) => ty2
        case _              => sys.error("tyInfer: expected pair type")
      }

    case Case(e, cases) => {
      val variantType = tyInfer(ctx, e)
      variantType match {
        case TyVariant(tys) => {
          val casesMap = cases.toMap
          val (l, (x, e0)) = cases.head
          val ty0 = tys.getOrElse(l, sys.error("case not found"))
          val new_ctx = ctx + (x -> ty0)
          val inferredType = tyInfer(new_ctx, e0)
          tys.foreach { case (l, ty) =>
            casesMap.get(l) match {
              case Some((x, e0)) =>
                val new_ctx = ctx + (x -> ty)
                tyCheck(new_ctx, e0, inferredType)
              case None => sys.error("tyInfer: not exhaustive case")
            }
          }
          inferredType
        }
        case _ => sys.error("tyInfer: expected variant type")
      }
    }

    // Bag
    case Bag(elem :: elems) =>
      // infer first type
      val ty = tyInfer(ctx, elem)
      elems match {
        case Nil => TyBag(ty)
        case _   =>
          // check all elements have the same type
          elems.foreach(e => tyCheck(ctx, e, ty))
          TyBag(ty)
      }

    case FlatMap(e1, e2) =>
      // infer e1 type
      val e1_type = tyInfer(ctx, e1)
      e1_type match {
        case TyBag(ty1) =>
          // infer e2 type
          val e2_type = tyInfer(ctx, e2)
          e2_type match {
            case TyFun(ty_arg, TyBag(ty_res)) =>
              TyBag(ty_res)
            case _ => sys.error("tyInfer: expected function type")
          }
        case _ => sys.error("tyInfer: expected bag type")
      }

    case When(e1, e2) =>
      tyCheck(ctx, e2, TyBool)
      val e1_type = tyInfer(ctx, e2)
      e1_type match {
        case TyBag(ty) => TyBag(ty)
        case _         => sys.error("tyInfer: expected bag type")
      }

    case Sum(e1, e2) =>
      val e1_type = tyInfer(ctx, e1)
      e1_type match {
        case TyBag(ty) =>
          tyCheck(ctx, e2, TyBag(ty))
          TyBag(ty)
        case _ => sys.error("tyInfer: expected bag type")
      }

    case Diff(e1, e2) =>
      val e1_type = tyInfer(ctx, e1)
      e1_type match {
        case TyBag(ty) =>
          if (!isEqType(ty)) {
            sys.error("tyInfer: cannot diff on type " ++ ty.toString)
          }
          tyCheck(ctx, e2, TyBag(ty))
          TyBag(ty)
        case _ => sys.error("tyInfer: expected bag type")
      }

    case Count(e1, e2) =>
      val e1_type = tyInfer(ctx, e1)
      e1_type match {
        case TyBag(ty) =>
          tyCheck(ctx, e2, ty)
          if (!isEqType(ty)) {
            sys.error("tyInfer: cannot count on type " ++ ty.toString)
          }
          TyInt
        case _ => sys.error("tyInfer: expected bag type")
      }

    case Comprehension(e, Nil) =>
      val elemType = tyInfer(ctx, e)
      TyBag(elemType)

    case Comprehension(e, Bind(x, ei) :: es) =>
      // infer type of ei to be bag
      val elemType = tyInfer(ctx, ei)
      elemType match {
        case TyBag(tyPrime) =>
          val new_ctx = ctx + (x -> tyPrime)
          tyInfer(new_ctx, Comprehension(e, es))
        case _ => sys.error("tyInfer: expected bag type")
      }

    case Comprehension(e, CLet(x, ei) :: es) =>
      val elemType = tyInfer(ctx, ei)
      val new_ctx = ctx + (x -> elemType)
      tyInfer(new_ctx, Comprehension(e, es))

    case Comprehension(e, Guard(ei) :: es) =>
      tyCheck(ctx, ei, TyBool)
      tyInfer(ctx, Comprehension(e, es))

    // syntactic sugars
    case LetPair(x, y, e1, e2) =>
      val ty1 = tyInfer(ctx, e1)
      ty1 match {
        case TyPair(tyX, tyY) =>
          val newCtx = ctx + (x -> tyX) + (y -> tyY)
          tyInfer(newCtx, e2)
        case _ =>
          sys.error(
            "tyInfer: expected a pair type for the first expression in let pair"
          )
      }

    case LetFun(f, tyFun, x, e1, e2) =>
      tyFun match {
        case TyFun(ty1, ty2) =>
          val newCtxForE1 = ctx + (x -> ty1)
          tyCheck(newCtxForE1, e1, ty2)

          val newCtxForE2 = ctx + (f -> tyFun)
          tyInfer(newCtxForE2, e2)

        case _ =>
          sys.error(
            "tyInfer: expected function type for first expression in let fun"
          )
      }

    case LetRec(f, tyFun, x, e1, e2) =>
      tyFun match {
        case TyFun(ty1, ty2) =>
          val newCtxForE1 = ctx + (f -> tyFun) + (x -> ty1)
          tyCheck(newCtxForE1, e1, ty2)

          val newCtxForE2 = ctx + (f -> tyFun)
          val resultType = tyInfer(newCtxForE2, e2)

          resultType

        case _ =>
          sys.error(
            "tyInfer: expected function type for first expression in let rec"
          )
      }

    case LetRecord(xs, e1, e2) =>
      val ty1 = tyInfer(ctx, e1)
      ty1 match {
        case TyRecord(fields) =>
          val newCtx = xs.foldLeft(ctx) {
            case (currentCtx, (label, variable)) =>
              fields.get(label) match {
                case Some(fieldType) =>
                  currentCtx + (variable -> fieldType)
                case None =>
                  sys.error("tyInfer: field not found in record")
              }
          }
          tyInfer(newCtx, e2)
        case _ =>
          sys.error(
            "tyInfer: expected a record type for the first expression in let record"
          )
      }

    case _ => sys.error("tyInfer: expression not supported by tyInfer: " + e)
  }
}
