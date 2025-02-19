package Assign3.Interpreter

import Assign3.Parser.Parser
import Assign3.Syntax.Syntax._
import Assign3.Typer.Typer
import Assign3.Bags.Bags.BagImpl
import scala.collection.immutable.ListMap

object Interpreter {

  // ======================================================================
  // Capture-avoiding substitution
  // ======================================================================

  val generator = SymGenerator()

  object SubstExpr extends Substitutable[Expr] {
    // swap y and z in e
    def swap(e: Expr, y: Variable, z: Variable): Expr =
      def go(e: Expr): Expr = e match {
        // Value must be closed
        case v: Value => v

        case Unit => Unit

        case Num(n)        => Num(n)
        case Plus(e1, e2)  => Plus(go(e1), go(e2))
        case Minus(e1, e2) => Minus(go(e1), go(e2))
        case Times(e1, e2) => Times(go(e1), go(e2))

        case Bool(b)               => Bool(b)
        case Eq(e1, e2)            => Eq(go(e1), go(e2))
        case Less(e1, e2)          => Less(go(e1), go(e2))
        case IfThenElse(e, e1, e2) => IfThenElse(go(e), go(e1), go(e2))

        case Str(s)         => Str(s)
        case Length(e)      => Length(go(e))
        case Index(e1, e2)  => Index(go(e1), go(e2))
        case Concat(e1, e2) => Concat(go(e1), go(e2))

        case Var(x)         => Var(swapVar(x, y, z))
        case Let(x, e1, e2) => Let(swapVar(x, y, z), go(e1), go(e2))

        case Anno(e, ty) => Anno(go(e), ty)
        // case Inst(e, ty) => Inst(go(e), ty)

        case Pair(e1, e2) => Pair(go(e1), go(e2))
        case First(e)     => First(go(e))
        case Second(e)    => Second(go(e))

        case Lambda(x, e)  => Lambda(swapVar(x, y, z), go(e))
        case Apply(e1, e2) => Apply(go(e1), go(e2))
        case Rec(f, x, e)  => Rec(swapVar(f, y, z), swapVar(x, y, z), go(e))

        case Record(es) => Record(es.map((x, e) => (x, go(e))))
        case Proj(e, l) => Proj(go(e), l)

        case Variant(l, e) => Variant(l, go(e))
        case Case(e, cls) =>
          Case(
            go(e),
            cls.map((l, entry) =>
              val (x, e) = entry
              (l, (swapVar(x, y, z), go(e)))
            )
          )

        case Bag(es)              => Bag(es.map(e => go(e)))
        case FlatMap(e1, e2)      => FlatMap(go(e1), go(e2))
        case When(e1, e2)         => When(go(e1), go(e2))
        case Sum(e1, e2)          => Sum(go(e1), go(e2))
        case Diff(e1, e2)         => Diff(go(e1), go(e2))
        case Comprehension(e, es) => Comprehension(go(e), es.map(e => go(e)))
        case Bind(x, e)           => Bind(swapVar(x, y, z), go(e))
        case Guard(e)             => Guard(go(e))
        case CLet(x, e)           => CLet(swapVar(x, y, z), go(e))
        case Count(e1, e2)        => Count(go(e1), go(e2))

        case LetPair(x1, x2, e1, e2) =>
          LetPair(swapVar(x1, y, z), swapVar(x2, y, z), go(e1), go(e2))
        case LetFun(f, ty, x, e1, e2) =>
          LetFun(swapVar(f, y, z), ty, swapVar(x, y, z), go(e1), go(e2))
        case LetRec(f, ty, x, e1, e2) =>
          LetRec(swapVar(f, y, z), ty, swapVar(x, y, z), go(e1), go(e2))
        case LetRecord(xs, e1, e2) =>
          LetRecord(xs.map((l, x) => (l, swapVar(x, y, z))), go(e1), go(e2))
      }
      go(e)

    ////////////////////
    // EXERCISE 4     //
    ////////////////////
    def subst(e1: Expr, e2: Expr, x: Variable): Expr = {

      // e1 is being modified, e2 is going to replace x in e1
      e1 match {

        case Unit => Unit

        case v: Value => v

        // Int
        case Num(n) => Num(n)
        case Plus(expr1, expr2) =>
          Plus(subst(expr1, e2, x), subst(expr2, e2, x))
        case Minus(expr1, expr2) =>
          Minus(subst(expr1, e2, x), subst(expr2, e2, x))
        case Times(expr1, expr2) =>
          Times(subst(expr1, e2, x), subst(expr2, e2, x))

        // Bool
        case Bool(b)          => Bool(b)
        case Eq(expr1, expr2) => Eq(subst(expr1, e2, x), subst(expr2, e2, x))
        case Less(expr1, expr2) =>
          Less(subst(expr1, e2, x), subst(expr2, e2, x))
        case IfThenElse(expr, expr1, expr2) =>
          IfThenElse(
            subst(expr, e2, x),
            subst(expr1, e2, x),
            subst(expr2, e2, x)
          )

        // String
        case Str(s)       => Str(s)
        case Length(expr) => Length(subst(expr, e2, x))
        case Index(expr1, expr2) =>
          Index(subst(expr1, e2, x), subst(expr2, e2, x))
        case Concat(expr1, expr2) =>
          Concat(subst(expr1, e2, x), subst(expr2, e2, x))

        // Variable & Let
        case Var(v) => if (v == x) e2 else Var(v)
        case Let(v, expr1, expr2) => {
          val newV = generator.genVar(v)
          Let(newV, subst(expr1, e2, x), subst(swap(expr2, v, newV), e2, x))
        }

        // Anno
        case Anno(expr, ty) => Anno(subst(expr, e2, x), ty)

        // Functions
        case Lambda(v, expr) => {
          val newV = generator.genVar(v)
          Lambda(newV, subst(swap(expr, v, newV), e2, x))
        }
        case Apply(expr1, expr2) =>
          Apply(subst(expr1, e2, x), subst(expr2, e2, x))
        case Rec(f, v, expr) => {
          val newF = generator.genVar(f)
          val newV = generator.genVar(v)
          Rec(newF, newV, subst(swap(swap(expr, f, newF), v, newV), e2, x))
        }

        // Pair
        case Pair(expr1, expr2) =>
          Pair(subst(expr1, e2, x), subst(expr2, e2, x))
        case First(expr)  => First(subst(expr, e2, x))
        case Second(expr) => Second(subst(expr, e2, x))

        // Records
        case Record(fields) => {
          Record(fields.map((l, expr) => (l, subst(expr, e2, x))))
        }
        case Proj(expr, l) => Proj(subst(expr, e2, x), l)

        // Variants
        case Variant(l, expr) => Variant(l, subst(expr, e2, x))
        case Case(e0, cases) => {
          val newE0 = subst(e0, e2, x)
          val newCases = cases.map { case (label, (v, expr)) =>
            val newVar = generator.genVar(v)
            val swappedExpr = swap(expr, v, newVar)
            (label, (newVar, subst(swappedExpr, e2, x)))
          }
          Case(newE0, newCases)
        }
        
        // Bags
        case Bag(es) => Bag(es.map(e => subst(e, e2, x)))
        case When(expr1, expr2) =>
          When(subst(expr1, e2, x), subst(expr2, e2, x))
        case Sum(expr1, expr2) =>
          Sum(subst(expr1, e2, x), subst(expr2, e2, x))
        case Diff(expr1, expr2) =>
          Diff(subst(expr1, e2, x), subst(expr2, e2, x))
        case Count(expr1, expr2) =>
          Count(subst(expr1, e2, x), subst(expr2, e2, x))
        case FlatMap(expr1, expr2) =>
          FlatMap(subst(expr1, e2, x), subst(expr2, e2, x))

        // Comprehension
        case Comprehension(t0, ts) =>
          val newTs = ts.map {
            case Bind(y, e1_) =>
              val freshY = generator.genVar(y)
              val swappedExpr = swap(e1_, y, freshY)
              Bind(freshY, subst(swappedExpr, e2, x))
            case CLet(y, e1_) =>
              if (y == x) {
                CLet(y, subst(e1_, e2, x))
              } else {
                val freshY = generator.genVar(y)
                val swappedExpr = swap(e1_, y, freshY)
                CLet(freshY, subst(swappedExpr, e2, x))
              }
            case Guard(e1_) =>
              Guard(subst(e1_, e2, x))
            case expr =>
              subst(expr, e2, x)
          }
          val newT0 = subst(t0, e2, x)
          Comprehension(newT0, newTs)
        case Bind(v, e) => Bind(v, subst(e, e2, x))
        case Guard(e)   => Guard(subst(e, e2, x))
        case CLet(v, e) => CLet(v, subst(e, e2, x))

        // Syntactic Sugar
        case LetPair(v1, v2, expr1, expr2) => {
          val newV1 = generator.genVar(v1)
          val newV2 = generator.genVar(v2)
          // may have to swap around in the swap function
          LetPair(
            newV1,
            newV2,
            subst(expr1, e2, x),
            subst(swap(swap(expr2, v1, newV1), v2, newV2), e2, x)
          )
        }
        case LetFun(f, ty, v, expr1, expr2) => {
          val newF = generator.genVar(f)
          val newV = generator.genVar(v)
          LetFun(
            newF,
            ty,
            newV,
            subst(swap(expr1, v, newV), e2, x),
            subst(swap(expr2, f, newF), e2, x)
          )
        }
        case LetRec(f, ty, v, expr1, expr2) => {
          val newF = generator.genVar(f)
          val newV = generator.genVar(v)
          LetRec(
            newF,
            ty,
            newV,
            subst(swap(swap(expr1, f, newF), v, newV), e2, x),
            subst(swap(expr2, f, newF), e2, x)
          )
        }
        case LetRecord(xs, expr1, expr2) => {
          val newVars = xs.map((l, v) => (l, generator.genVar(v)))
          val substitutedExpr1 = subst(expr1, e2, x)
          val swappedExpr2 = xs
            .zip(newVars)
            .foldLeft(expr2)((acc, pair) => {
              val ((l, v), (l1, v1)) = pair
              swap(acc, v, v1)
            })
          val substitutedExpr2 = subst(swappedExpr2, e2, x)
          LetRecord(newVars, substitutedExpr1, substitutedExpr2)
        }
      }
    }
  }
  import SubstExpr.{subst}

  // ======================================================================
  // Desugaring and Type Erasure
  // ======================================================================

  ////////////////////
  // EXERCISE 5     //
  ////////////////////
  def desugar(e: Expr): Expr = e match {
    // Value
    case v: Value =>
      sys.error("desugar: there shouldn't be any values here")

    // unit
    case Unit => Unit

    // arithmetic expressions
    case Num(n)        => Num(n)
    case Plus(e1, e2)  => Plus(desugar(e1), desugar(e2))
    case Minus(e1, e2) => Minus(desugar(e1), desugar(e2))
    case Times(e1, e2) => Times(desugar(e1), desugar(e2))

    // boolean
    case Bool(b)      => Bool(b)
    case Eq(e1, e2)   => Eq(desugar(e1), desugar(e2))
    case Less(e1, e2) => Less(desugar(e1), desugar(e2))
    case IfThenElse(cond, e1, e2) => {
      IfThenElse(desugar(cond), desugar(e1), desugar(e2))
    }

    // strings
    case Str(s)         => Str(s)
    case Length(e)      => Length(desugar(e))
    case Index(e1, e2)  => Index(desugar(e1), desugar(e2))
    case Concat(e1, e2) => Concat(desugar(e1), desugar(e2))

    // var and let
    case Let(x, e1, e2) => Let(x, desugar(e1), desugar(e2))
    case Var(x)         => Var(x)

    // annotations
    case Anno(e, ty) => desugar(e)

    // functions
    case Lambda(x, e)  => Lambda(x, desugar(e))
    case Apply(e1, e2) => Apply(desugar(e1), desugar(e2))
    case Rec(f, x, e)  => Rec(f, x, desugar(e))

    // pairing
    case Pair(e1, e2) => Pair(desugar(e1), desugar(e2))
    case First(e)     => First(desugar(e))
    case Second(e)    => Second(desugar(e))

    // records
    case Record(es) =>
      Record(es.map { case (label, expr) => (label, desugar(expr)) })
    case Proj(e, l) => Proj(desugar(e), l)

    // variants
    case Variant(l, e) => Variant(l, desugar(e))
    case Case(e, cls) =>
      Case(
        desugar(e),
        cls.map { case (label, (x, body)) => (label, (x, desugar(body))) }
      )

    // bags
    case Bag(es)         => Bag(es.map(desugar))
    case FlatMap(e1, e2) => FlatMap(desugar(e1), desugar(e2))
    case When(e1, e2)    => When(desugar(e1), desugar(e2))
    case Sum(e1, e2)     => Sum(desugar(e1), desugar(e2))
    case Diff(e1, e2)    => Diff(desugar(e1), desugar(e2))
    case Count(e1, e2)   => Count(desugar(e1), desugar(e2))

    // comprehensions
    case Comprehension(e, Nil) => Bag(List(desugar(e)))
    case Comprehension(e, Bind(x, e_pr) :: ps) => {
      FlatMap(desugar(e_pr), Lambda(x, desugar(Comprehension(e, ps))))
    }
    case Comprehension(e, CLet(x, e_pr) :: ps) => {
      Let(x, desugar(e_pr), desugar(Comprehension(e, ps)))
    }
    case Comprehension(e, Guard(e_pr) :: ps) => {
      When(desugar(e_pr), desugar(Comprehension(e, ps)))
    }
    case Comprehension(e, _) => sys.error("desugar: Invalid syntax")
    case Bind(x, e)          => Bind(x, desugar(e))
    case Guard(e)            => Guard(desugar(e))
    case CLet(x, e)          => CLet(x, desugar(e))

    // syntactic sugar
    case LetFun(f, ty, x, e1, e2) =>
      Let(f, Lambda(x, desugar(e1)), desugar(e2))
    case LetRec(f, ty, x, e1, e2) =>
      Let(f, Rec(f, x, desugar(e1)), desugar(e2))
    case LetRecord(xs, e1, e2) => {
      val r = generator.freshVar()
      val desugaredE1 = desugar(e1)
      val substitutedE2 = xs.foldLeft(desugar(e2)) {
        case (acc, (label, variable)) =>
          subst(acc, Proj(Var(r), label), variable)
      }
      Let(r, desugaredE1, substitutedE2)
    }
    case LetPair(x, y, e1, e2) => {
      val p = generator.genVar("p")
      Let(
        p,
        desugar(e1),
        subst(subst(desugar(e2), First(Var(p)), x), Second(Var(p)), y)
      )
    }
  }

  // ======================================================================
  // Primitive operations
  // ======================================================================

  object Value {
    // utility methods for operating on values
    def add(v1: Value, v2: Value): Value = (v1, v2) match
      case (NumV(v1), NumV(v2)) => NumV(v1 + v2)
      case _ => sys.error("arguments to addition are non-numeric")

    def subtract(v1: Value, v2: Value): Value = (v1, v2) match
      case (NumV(v1), NumV(v2)) => NumV(v1 - v2)
      case _ => sys.error("arguments to subtraction are non-numeric")

    def multiply(v1: Value, v2: Value): Value = (v1, v2) match
      case (NumV(v1), NumV(v2)) => NumV(v1 * v2)
      case _ => sys.error("arguments to multiplication are non-numeric")

    def eq(v1: Value, v2: Value): Value = (v1, v2) match
      case (NumV(v1), NumV(v2))               => BoolV(v1 == v2)
      case (BoolV(v1), BoolV(v2))             => BoolV(v1 == v2)
      case (StringV(v1), StringV(v2))         => BoolV(v1 == v2)
      case (PairV(v11, v12), PairV(v21, v22)) => BoolV(v11 == v21 && v12 == v22)
      case (VariantV(l1, v1), VariantV(l2, v2)) => BoolV(l1 == l2 && v1 == v2)
      // no comparision for bags and records currently
      case _ => sys.error("arguments to = are not comparable")

    def less(v1: Value, v2: Value): Value = (v1, v2) match
      case (NumV(v1), NumV(v2)) => BoolV(v1 < v2)
      case _ => sys.error("arguments to < are not comparable")

    def length(v: Value): Value = v match
      case StringV(v1) => NumV(v1.length)
      case _           => sys.error("argument to length is not a string")

    def index(v1: Value, v2: Value): Value = (v1, v2) match
      case (StringV(v1), NumV(v2)) => StringV(v1.charAt(v2).toString)
      case _ => sys.error("arguments to index are not valid")

    def concat(v1: Value, v2: Value): Value = (v1, v2) match
      case (StringV(v1), StringV(v2)) => StringV(v1 ++ v2)
      case _ => sys.error("arguments to concat are not strings")
  }

  // ======================================================================
  // Evaluation
  // ======================================================================

  ////////////////////
  // EXERCISE 6     //
  ////////////////////
  def eval(e: Expr): Value = e match {
    // Value
    case v: Value => v

    case Unit => UnitV

    // arithmetic expressions
    case Num(n) => NumV(n)
    case Plus(e1, e2) =>
      Value.add(eval(e1), eval(e2))
    case Minus(e1, e2) =>
      Value.subtract(eval(e1), eval(e2))
    case Times(e1, e2) =>
      Value.multiply(eval(e1), eval(e2))

    // booleans
    case Bool(b)      => BoolV(b)
    case Eq(e1, e2)   => Value.eq(eval(e1), eval(e2))
    case Less(e1, e2) => Value.less(eval(e1), eval(e2))
    case IfThenElse(cond, e1, e2) =>
      eval(cond) match {
        case BoolV(true)  => eval(e1)
        case BoolV(false) => eval(e2)
        case _            => sys.error("eval: condition is not a boolean")
      }

    // strings
    case Str(s)         => StringV(s)
    case Length(expr)   => Value.length(eval(expr))
    case Index(e1, e2)  => Value.index(eval(e1), eval(e2))
    case Concat(e1, e2) => Value.concat(eval(e1), eval(e2))

    // Variable and Let
    case Var(x) => sys.error("eval: variable is not bound")
    case Let(x, e1, e2) => {
      val e1Eval = eval(e1)
      eval(subst(e2, e1Eval, x))
    }

    // annotations
    case Anno(e, ty) => sys.error("eval: type annotation should not reach here")

    // functions
    case Apply(e1, e2) =>
      eval(e1) match {
        // lambda case
        case FunV(x, e) => eval(subst(e, eval(e2), x))
        // recursive function case
        case RecV(f, x, body) => {
          val funcClosure = subst(body, RecV(f, x, body), f)
          val argumentSubstituted = subst(funcClosure, eval(e2), x)
          eval(argumentSubstituted)
        }
        case _ => sys.error("eval: not a function")
      }
    case Rec(f, x, e) => RecV(f, x, e)
    case Lambda(x, e) => FunV(x, e)

    // pairing
    case Pair(e1, e2) => PairV(eval(e1), eval(e2))
    case First(e) =>
      eval(e) match {
        case PairV(v1, v2) => v1
        case _             => sys.error("eval: not a pair")
      }
    case Second(e) =>
      eval(e) match {
        case PairV(v1, v2) => v2
        case _             => sys.error("eval: not a pair")
      }

    // records
    case Record(es) =>
      RecordV(es.map { case (label, expr) => (label, eval(expr)) })
    case Proj(expr, l) =>
      eval(expr) match {
        case RecordV(es) => es.getOrElse(l, sys.error("eval: label not found"))
        case _           => sys.error("eval: not a record")
      }

    // variants
    case Variant(l, expr) => VariantV(l, eval(expr))
    case Case(expr, cls) =>
      eval(expr) match {
        case VariantV(l, v) =>
          cls(l) match {
            case (x, e) => eval(subst(e, v, x))
          }
        case _ => sys.error("eval: not a variant")
      }

    // bags
    case Bag(es) => BagV(es.map(x => eval(x)))
    case FlatMap(e1, e2) => 
      eval(e1) match {
        case BagV(es) =>
          eval (e2) match {
            case FunV(x, body) =>
              val mappedBags = BagImpl.flatMap (es, (element) => {
                eval(subst(body, element, x)) match {
                  case BagV(innerBag) => innerBag
                  case _ => sys.error("eval: expect a function that returns a bag")
                }
              })
              BagV(mappedBags)
            case RecV(f, x, body) =>
              val mappedBags = BagImpl.flatMap (es, (element) => {
                val bodyWithRec = subst(body, RecV(f, x, body), f)
                eval(subst(bodyWithRec, element, x)) match {
                  case BagV(innerBag) => innerBag
                  case _ => sys.error("eval: expect a recursive function that returns a bag")
                }
              })
              BagV(mappedBags)
            case _ => sys.error("eval: expect a function or recursive function that returns a bag")
          }
        case _ => sys.error("eval: expects a bag as the first argument")
      }
    case When(e1, e2) => {
      val e1_val = eval(e1)
      val e2_val = eval(e2)
      e1_val match
        case BoolV(true)  => e2_val
        case BoolV(false) => BagV(List())
        case _            => sys.error("not a boolean" + e1_val + e2_val)
    }
    case Sum(e1, e2) =>
      (eval(e1), eval(e2)) match {
        case (BagV(es1), BagV(es2)) => BagV(BagImpl.sum(es1, es2))
        case _ => sys.error("eval: Expected bags for Sum")
      }
    case Diff(e1, e2) =>
      (eval(e1), eval(e2)) match {
        case (BagV(es1), BagV(es2)) => BagV(BagImpl.diff(es1, es2))
        case _ => sys.error("eval: Expected bags for Diff")
      }
    case Count(e1, e2) =>
      val target = eval(e2)
      eval(e1) match {
        case BagV(es) => NumV(BagImpl.count(es, target))
        case _        => sys.error("eval: Expected a bag for Count")
      }

    // all of these should have been desugared
    // syntactic sugar
    case LetFun(f, ty, arg, e1, e2) =>
      sys.error("eval: LetFun should not reach here")
    case LetRec(f, ty, arg, e1, e2) =>
      sys.error("eval: LetRec should not reach here")
    case LetRecord(xs, e1, e2) =>
      sys.error("eval: LetRecord should not reach here")
    case LetPair(x, y, e1, e2) =>
      sys.error("eval: LetPair should not reach here")

    // comprehensions
    case Comprehension(e, _) =>
      sys.error("eval: Comprehension should not reach here")
    case Bind(x, e) => sys.error("eval: Bind should not reach here")
    case Guard(e)   => sys.error("eval: Guard should not reach here")
    case CLet(x, e) => sys.error("eval: CLet should not reach here")
  }

  /////////////////////////////////////////////////////////
  // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! //
  // THE REST OF THIS FILE SHOULD NOT NEED TO BE CHANGED //
  // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! //
  /////////////////////////////////////////////////////////

  // ======================================================================
  // Some simple programs
  // ======================================================================

  // The following examples illustrate how to embed Frog source code into
  // Scala using multi-line comments, and parse it using parser.parseStr.

  // Example 1: the swap function
  def example1: Expr = parser.parseStr("""
    let swap = \ x . (snd(x), fst(x)) in
    swap(42,17)
    """)

  val parser = new Parser

  // ======================================================================
  // Main
  // ======================================================================

  object Main {
    def typecheck(ast: Expr): Type =
      Typer.tyInfer(ListMap(), ast);

    def evaluate(ast: Expr): Value =
      eval(ast)

    def showResult(ast: Expr) = {
      println("AST:  " + ast.toString + "\n")

      try {
        print("Type Checking...");
        val ty = typecheck(ast);
        println("Done!");
        println("Type of Expression: " + ty.toString + "\n");
      } catch {
        case e: Throwable => println("Error: " + e)
      }
      try {
        println("Desugaring...");
        val core_ast = desugar(ast);
        println("Done!");
        println("Desugared AST: " + core_ast.toString + "\n");

        println("Evaluating...");
        println("Result: " + evaluate(core_ast))
      } catch {
        case e: Throwable => {
          println("Error: " + e)
          println("Evaluating raw AST...");
          println("Result: " + evaluate(ast))
        }
      }
    }

    def start(): Unit = {
      println("Welcome to Frog! (V1.0, October 22, 2024)");
      println(
        "Enter expressions to evaluate, :load <filename.fish> to load a file, or :quit to quit."
      );
      println(
        "This REPL can only read one line at a time, use :load to load larger expressions."
      );
      repl()
    }

    def repl(): Unit = {
      print("Frog> ");
      val input = scala.io.StdIn.readLine();
      if (input == ":quit") {
        println("Goodbye!")
      } else if (input.startsWith(":load")) {
        try {
          val ast = parser.parse(input.substring(6));
          showResult(ast)
        } catch {
          case e: Throwable => println("Error: " + e)
        }
        repl()
      } else {
        try {
          val ast = parser.parseStr(input);
          showResult(ast)
        } catch {
          case e: Throwable => println("Error: " + e)
        }
        repl()
      }
    }
  }

  def main(args: Array[String]): Unit = {
    if (args.length == 0) {
      Main.start()
    } else {
      try {
        print("Parsing...");
        val ast = parser.parse(args.head)
        println("Done!");
        Main.showResult(ast)
      } catch {
        case e: Throwable => println("Error: " + e)
      }
    }
  }

}
