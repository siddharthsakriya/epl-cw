import Assign3.Syntax.Syntax._
import Assign3.Interpreter._

val subst = Interpreter.SubstExpr.subst

val parser = Interpreter.parser

val desugar = Interpreter.desugar

val eval = Interpreter.eval

def aequiv(e1: Expr, e2:Expr): Boolean = {
  def equivVar(l: List[(Variable,Variable)], v1: Variable, v2: Variable): Boolean = l match {
    case Nil => v1 == v2
    case (x1,x2)::xs =>
      if (v1 == x1 || v2 == x2) {
        v1 == x1 && v2 == x2
      } else {
        equivVar(xs,v1,v2)
      }
  };
  def go(l: List[(Variable,Variable)], e1: Expr, e2: Expr): Boolean = (e1,e2) match {
    case (Unit, Unit) => true

    case (Num(n), Num(m)) => n == m
    case (Plus(e11,e12), Plus(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)
    case (Times(e11,e12), Times(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)
    case (Minus(e11,e12), Minus(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)

    case (Bool(b1), Bool(b2)) => b1 == b2
    case (Eq(e11,e12), Eq(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)
    case (IfThenElse(e10,e11,e12), IfThenElse(e20,e21,e22)) =>
      go(l,e10,e20) && go(l,e11,e21) && go(l,e12,e22)

    case (Str(s1), Str(s2)) => s1 == s2
    case (Length(e1), Length(e2)) =>
      go(l,e1,e2)
    case (Index(e11,e12), Index(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)
    case (Concat(e11,e12), Concat(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)

    case (Var(v1),Var(v2)) => equivVar(l,v1,v2)
    case (Let(x1,e11,e12),Let(x2,e21,e22)) =>
      go(l,e11,e21) && go((x1,x2)::l,e12,e22)
    case (LetFun(f1,_,x1,e11,e12),LetFun(f2,_,x2,e21,e22)) =>
      go((x1,x2)::l,e11,e21) && go((f1,f2)::l,e12,e22)
    case (LetRec(f1,_,x1,e11,e12),LetRec(f2,_,x2,e21,e22)) =>
      go((f1,f2)::(x1,x2)::l,e11,e21) && go((f1,f2)::l,e12,e22)
    case (LetPair(x1,y1,e11,e12), LetPair(x2,y2,e21,e22)) =>
      go(l,e11,e21) && go((x1,x2)::(y1,y2)::l, e12,e22)
    case (LetRecord(xs1,e11,e12),LetRecord(xs2,e21,e22)) =>
      // assumes no variables repeated
      if xs1.keys != xs2.keys then false
      else {
        val vars = xs1.keys.map{(k) => (xs1(k),xs2(k))}.toList
        go(l,e11,e12) && go(vars ++ l,e12,e22)
      }

    case (Pair(e11,e12), Pair(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)
    case (First(e1), First(e2)) =>
      go(l,e1,e2)
    case (Second(e1), Second(e2)) =>
      go(l,e1,e2)

    case (Lambda(x1,e1),Lambda(x2,e2)) =>
      go((x1,x2)::l,e1,e2)
    case (Apply(e11,e12), Apply(e21,e22)) =>
      go(l,e11,e21) && go(l,e12,e22)
    case (Rec(f1,x1,e1),Rec(f2,x2,e2)) =>
        go((f1,f2)::(x1,x2)::l,e1,e2)

    case (Record(es1),Record(es2)) =>
      es1.keys == es2.keys &&
        es1.keys.forall{(k) => go(l,es1(k),es2(k))}
    case (Proj(e1,l1),Proj(e2,l2)) =>
      l1 == l2 && go(l,e1,e2)

    case (Variant(l1,e1),Variant(l2,e2)) =>
      l1 == l2 && go(l,e1,e2)
    case (Case(e1,cls1),Case(e2,cls2)) =>
      cls1.keys == cls2.keys &&
        cls1.keys.forall{(k) =>
          val (x1,e1) = cls1(k)
          val (x2,e2) = cls2(k)
          go((x1,x2)::l,e1,e2)
        }

    case (Anno(e1,t1),Anno(e2,t2)) => go(l,e1,e2)

    case (Bag(e1),Bag(e2)) => e1.zip(e2).forall{case (x,y) => go(l,x,y)}
    case (FlatMap(e11,e12),FlatMap(e21,e22)) => 
      go(l,e11,e21) && go(l,e12,e22)
    case (When(e11,e12),When(e21,e22)) => 
      go(l,e11,e21) && go(l,e12,e22)
    case (e1,e2) => e1 == e2
    // NOTE: α-equivalence for bag-relevant expressions is not implemented yet.
  };
  go(Nil,e1,e2)
}

lazy val substExp1: Boolean = aequiv(
  subst(
    parser.parseStr("""
        (\y.x + y) x
       """), parser.parseStr("(y+y)"),
    "x"),
  parser.parseStr("""
        (\z.(y + y) + z) (y+y)
       """))


lazy val substExp2: Boolean = aequiv(
    subst(
      parser.parseStr("""
        let y = x in
        x + y
       """), parser.parseStr("(y+y)"),
      "x"),
      parser.parseStr("""
        let z = (y + y) in (y + y) + z
       """))

lazy val substExp3: Boolean =
  aequiv(
    subst(
      parser.parseStr("""
        (rec f (y).
          if (y == 0) then
            y else
            x + f(y - 1))
        y
       """),
      parser.parseStr("f y"),
      "x"),
    parser.parseStr("""
        (rec g (z).
          if (z == 0) then
            z else
            (f y) + g(z - 1))
        y
       """))

lazy val substExp4: Boolean = aequiv(
  subst(
    desugar(parser.parseStr("""
        let (y,z) = (x,x+1) in
        x + y + z
       """)), parser.parseStr("(y*z)"),
    "x"),
    desugar(parser.parseStr("""
        let (a,b) = ((y*z),(y*z)+1) in
        (y*z) + a + b
       """)))

lazy val substExp5: Boolean = aequiv(
  subst(
    desugar(parser.parseStr("""
        sig f: int -> int let fun f(y) = x + y in f x
       """)), parser.parseStr("(y+y)"),
    "x"),
     desugar( parser.parseStr("""
        sig f: int -> int let fun f(z) = (y+y) + z in f (y+y)
       """)))

lazy val substExp6: Boolean =
  aequiv(
    subst(
      desugar(parser.parseStr("""
        sig f: int -> int let rec f (y) =
          if (y == 0) then
            y else
            x + f(y - 1)
        in f y
       """)),
      parser.parseStr("f y"),
      "x"),
    desugar(parser.parseStr("""
        sig g: int -> int let rec g (z) =
          if (z == 0) then
            z else
            (f y) + g(z - 1)
        in g y
       """)))



lazy val substExp7: Boolean =
  eval(
    subst(desugar(parser.parseStr("""sig f: int -> int let rec f(x) = x+1 in f 12""")),Num(14),"x")) == NumV(13)


lazy val substExp8: Boolean =
  eval(
    subst(desugar(parser.parseStr("""sig x: int -> int let rec x (y) = if y == 12 then x (y+1) else (y+1) in x 12""")),Num(26),"x")) == NumV(14)

lazy val substExp9: Boolean =
  aequiv(subst(Rec("f","x",Plus(Num(2),Var("x"))),Num(20),"x"), Rec("f","x",Plus(Num(2),Var("x"))))


lazy val substExp10: Boolean =
  eval(
    subst(desugar(parser.parseStr("""let (a,b) = (12,13) in (sig f:int -> int let rec f (x) = x+1 in f a)""")),Num(14),"x")) == NumV(13)

lazy val substExp11: Boolean =
  eval(
    subst(desugar(parser.parseStr("""let (a,b) = (12,13) in (sig f:int->int let fun f(x) = x+1 in f a)""")),Num(14),"x")) == NumV(13)

lazy val substExp12: Boolean =
  eval(
    subst(desugar(parser.parseStr("""let (a,b) = (12,13) in (sig f:int->int let rec f(x) = x+1 in f a)""")),Num(14),"x")) == NumV(13)

lazy val substExp13: Boolean =
  aequiv(
    subst(
      desugar(parser.parseStr("""
      {|y | let x = 4, let y = x + 1|}
       """)),
      parser.parseStr("2"),
      "x"),
    desugar(parser.parseStr("""
      {|y | let x = 4, let y = x + 1|}
       """)))

def test(name: String, test: Boolean) = {
  println(name + ": " + (if test then "passed" else "failed"))
}

@main def runTests() = {

  test("substExp1",substExp1)
  test("substExp2",substExp2)
  test("substExp3",substExp3)
  test("substExp4",substExp4)
  test("substExp5",substExp5)
  test("substExp6",substExp6)
  test("substExp7",substExp7)
  test("substExp8",substExp8)
  test("substExp9",substExp9)
  test("substExp10",substExp10)
  test("substExp11",substExp11)
  test("substExp12",substExp12)
  test("substExp13",substExp13)
}
