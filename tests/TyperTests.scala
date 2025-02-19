import scala.collection.immutable.ListMap

import Assign3.Syntax.Syntax._
import Assign3.Typer._
import Assign3.Interpreter._

val tyCheck = Typer.tyCheck

val tyInfer = Typer.tyInfer

val parser = Interpreter.parser

val emptyEnv = ListMap[Variable, Type]()

def check(e: Expr, t: Type): Unit = tyCheck(emptyEnv, e, t)

def exp(s: String): Expr = parser.parseStr(s)

def typ(s: String): Type = parser.parseTyStr(s)

// Test begin

val testTy0 = (
  "identity function",
  () => exp("\\x . x"),
  () => typ("int -> int")
)

val testTy1 = (
  "first",
  () => exp("\\x . fst(x)"),
  () => typ("int * bool -> int")
)

val testTy2 = (
  "projection",
  () => exp("sig f : <foo: int> -> int let fun f(x) = x.foo + 42 in f <foo = 0>"),
  () => typ("int")
)

val testTy3 = (
  "advanced projection",
  () => exp("sig f : <foo: int> -> int let fun f(x) = x.foo + 42 in f <foo = 42, bar = true>"),
  () => typ("int")
)

val testTy4 = (
  "case split",
  () => exp("""
  sig g : [foo: int, bar: bool] -> int
  let fun g(x) = case x of {
    foo x -> x,
    bar b -> if b then 42 else 37
  } in g (select bar true)"""),
  () => typ("int")
)

val testTy5 = (
  "annotation and subtyping",
  () => exp("""
  sig g : [foo: int, bar: bool] -> int
  let fun g(x) = case x of {
    foo x -> x,
    bar b -> if b then 42 else 37
  } in g ((select foo 6) : [foo: int])
  """),
  () => typ("int")
)

val testTy6 = (
  "nested subtyping",
  () => exp("sig f : <foo: <bar: int>> -> int let fun f(x) = x.foo.bar in f <foo = <bar = 42, baz = 37>>"),
  () => typ("int")
)

val testTy7 = (
  "power",
  () => exp("""
  rec power (input) .
  let x = fst(input) in
  let n = snd(input) in
  if (n == 0) then 1
  else x * power(x,n-1)
  """),
  () => typ("int * int -> int")
)

val testTy8 = (
  "bags",
  () => exp("""
  let piBag = {|3, 1, 4, 1, 5, 9|} in
  {| x + z | x <- piBag, 4 < x, y <- piBag, let z = y * y |}
  """),
  () => typ("{|int|}")
)


def test(pack: (String, () => Expr, () => Type)) =
  val (s, e, ty) = pack
  print("Running <" ++ s ++ ">.")
  var noError = true
  try {
    check(e(), ty())
  } catch {
    case _:Throwable => {
      println(" Failed.") // Run the program separately to see more useful error message.
      noError = false
    }
  }
  if noError then println(" Passed.") else ()

@main def runTests() = {
  test(testTy0)
  test(testTy1)
  test(testTy2)
  test(testTy3)
  test(testTy4)
  test(testTy5)
  test(testTy6)
  test(testTy7)
  test(testTy8)
}
