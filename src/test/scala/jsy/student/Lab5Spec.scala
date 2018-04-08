package jsy.student

import jsy.lab5.Lab5Like
import jsy.lab5.ast._
import jsy.lab5.Parser.parse
import jsy.tester.JavascriptyTester
import jsy.util.DoWith
import jsy.util.DoWith._
import org.scalatest._

class Lab5Spec(lab5: Lab5Like) extends FlatSpec {
  import lab5._

  "mapFirstDoWith" should "map the first element where f returns Some" in {
     val l1 = List(1, 2, -3, 4, -5)
     val gold1 = List(1, 2, 3, 4, -5)
     def dowith[W]: DoWith[W,List[Int]] = mapFirstWith(l1) { (i: Int) => if (i < 0) Some(doreturn(-i)) else None }
     assertResult((true,gold1)) { dowith(true) }
     assertResult((42,gold1)) { dowith(42) }
  }

  "mapWith(List)" should "map the elements of a list in a DoWith" in {
    val l = List(1, 2, 3, 4, 5)
    val r1 = l.map { i => i + 1 }

    def dowith1[W]: DoWith[W,List[Int]] = mapWith(l) { i: Int => doreturn(i + 1) }
    assertResult((true,r1)) { dowith1(true) }
    assertResult((42,r1)) { dowith1(42) }

    assertResult((2 * l.length + 1, r1)) {
      val dw: DoWith[Int,List[Int]] = mapWith(l) { i: Int =>
        domodify[Int](s => s + 2) map { _ => i + 1 }
      }
      dw(1)
    }
  }

  "rename" should "rename in a DoWith" in {
    val e1 = parse("const a = 1 + a; a")
    val e1p = parse("const aa = 1 + a; aa")

    assertResult((1,e1p)) {
      rename(empty, e1){ x => domodify[Int](n => n + 1) map { _ => x + x } }(0)
    }
  }

  "uniquify" should "uniquify with a counter for each variable" in {
    val e1 = parse("const a = 1; a")
    val e1p = parse("const a1 = 1; a1")
    val e2 = parse("const b = 2; b")
    val e2p = parse("const b0 = 2; b0")
    val e = Decl(MConst, "a", e1, e2)
    val ep = Decl(MConst, "a0", e1p, e2p)
    assertResult(ep) { uniquify(e) }
  }


  /* Tests based on rules */

  "CastOkNull" should "perform CastOkNull" in {
    assertResult(true) {
      castOk(TNull, TObj(Map.empty))
    }
  }

  "DoNeg" should "return the negation of a number value" in {
    val e1 = N(5)
    val e2 = Unary(Neg, e1)
    assertResult( N(-5) ) {
      val (_, r) = step(e2)(memempty)
      r
    }
  }

  // Probably want to write some tests for castOk, typeInfer, substitute, and step.
  "TypeVar" should "perform TypeVar" in {
    val xtype = TNumber
    val tenvx = extend(empty, "x", MTyp(MConst,xtype))
    assertResult(xtype) {
      typeof(tenvx, Var("x"))
    }
  }

  "TypeArith" should "perform TypeArith" in {
    assertResult(TNumber) {
      typeof(empty, Binary(Plus, N(1.0), N(1.0)))
    }
    assertResult(TNumber) {
      typeof(empty, Binary(Plus, Unary(Neg, N(1)), Binary(Div, N(2.0), N(3.0))))
    }
  }
  // custom tests
  "TypeNeg" should "perform TypeNeg" in {
    assertResult(TNumber){
      typeof(empty, Unary(Neg,N(1.0)))
    }
    intercept[StaticTypeError]{
      typeof(empty,Unary(Neg, S("hi")))
    }
  }
  "TypeNot" should "perform TypeNot" in {
    assertResult(TBool){
      typeof(empty, Unary(Not, B(true)))
    }
    intercept[StaticTypeError]{
      typeof(empty,Unary(Not, N(1.0)))
    }
  }
  "TypeSeq" should "perform TypeSeq" in {
    assertResult(TBool) {
      typeof(empty, Binary(Seq, B(false), Unary(Not, B(true))))
    }
    intercept[StaticTypeError] {
      typeof(empty, Binary(Seq, Unary(Not, N(1.0)), Unary(Not, B(true))))
    }
  }
  "TypeArith and TypePlusString" should "perform TypeArith and TypePlusString" in {
    assertResult(TNumber){
      typeof(empty, Binary(Plus, N(15),N(21)))
    }
    assertResult(TNumber){
      typeof(empty, Binary(Minus, N(15),N(21)))
    }
    assertResult(TString){
      typeof(empty, Binary(Plus, S("hi"), S("asdf")))
    }
    intercept[StaticTypeError]{
      typeof(empty,Binary(Plus, S("hi"), N(1.0)))
    }
    intercept[StaticTypeError]{
      typeof(empty, Binary(Minus, S("hi"), S("bye")))
    }
  }
  "TypeInequality (String and Number)" should "TypeInequality (string and number)" in{
    assertResult(TBool){
      typeof(empty, Binary(Ge, N(15), Binary(Plus, N(1.0), N(9.0))))
    }
    assertResult(TBool){
      typeof(empty, Binary(Lt, S("asdf"), S("asdf")))
    }
    intercept[StaticTypeError]{
      typeof(empty,Binary(Gt, Binary(Lt, S("asdf"), S("asdf")), Binary(Plus, N(1.0), N(9.0))))
    }
    intercept[StaticTypeError]{
      typeof(empty, Binary(Le, Print(S("hi")),Print(S("bye"))))
    }
  }
  "TypeCall" should "perform TypeCall" in {
    assertResult(TNumber){
      typeof(empty, Call(Function(None, List(("x", MTyp(MConst, TNumber)), ("y", MTyp(MConst, TNumber))), None, Binary(Plus,Var("x"), Var("y"))), List(N(1.0), N(2.0))))
    }
    assertResult(TBool){
      typeof(empty, Call(Function(None, List(("x", MTyp(MConst, TString)), ("y", MTyp(MConst, TString))), None, Binary(Le,Var("x"), Var("y"))), List(S("hi"), S("lajsf"))))
    }
  }
  "TypeRecFunction" should "perform TypeRecFunction" in {
    assertResult(TFunction(List(("n",MTyp(MConst,TNumber))), TNumber)){
      typeof(empty, Function(Some("f"),List(("n",MTyp(MConst,TNumber))),Some(TNumber),If(Binary(Eq,Var("n"),N(0.0)),N(0.0),Call(Var("f"),List(Binary(Minus,N(1.0),N(1.0)))))))
    }
  }
  "TypeObject" should "perform TypeObject" in {
    assertResult(TObj(Map("a" -> TNumber, "b" -> TString, "c" -> TUndefined))){
      typeof(empty, Obj(Map("b" -> Binary(Plus, S("hi"), S("bye")), "a" -> Unary(Neg, N(7)), "c" -> Print(S("print this")))))
    }
    assertResult(TObj(Map("a" -> TNumber, "b" -> TBool, "c" -> TUndefined))){
      typeof(empty, Obj(Map("b" -> Binary(Le, S("hi"), S("bye")), "a" -> Unary(Neg, N(7)), "c" -> Print(S("print this")))))
    }
    intercept[StaticTypeError] {
      typeof(empty, Obj(Map("b" -> Binary(Minus, S("hi"), S("bye")), "a" -> Unary(Neg, N(7)), "c" -> Print(S("print this")))))
    }
  }
  "TypeGetField" should "perform GetField" in {
    assertResult(TString) {
      typeof(empty, GetField(Obj(Map("b" -> Binary(Plus, S("hi"), S("bye")), "a" -> Unary(Neg, N(7)), "c" -> Print(S("print this")))), "b"))
    }
    assertResult(TUndefined){
      typeof(empty, GetField(Obj(Map("b" -> Binary(Plus, S("hi"), S("bye")), "a" -> Unary(Neg, N(7)), "c" -> Print(S("print this")))), "c"))
    }
    intercept[StaticTypeError]{
      typeof(empty, GetField(Obj(Map("b" -> Binary(Minus, S("hi"), S("bye")), "a" -> Unary(Neg, N(7)), "c" -> Print(S("print this")))), "b"))
    }
  }
  /* Substitute Tests from Lab 4*/
  "substitute" should "perform proper substitutes" in {
    assertResult(Decl(MConst, "a$", N(1.0), Binary(Plus, Var("a$"), Binary(Plus, Var("a"), N(2.0))))) { // example with renaming (const a = 1; a+b) [b\ a +2]
      substitute(Decl(MConst, "a", N(1.0), Binary(Plus, Var("a"), Var("b"))), Binary(Plus, Var("a"), N(2.0)), "b")
    }
  }

  /* Step Tests from Lab4*/
  "DoNot" should "perform DoNot" in {
    assertResult(B(false)){
      val (_,r) = step(Unary(Not, B(true)))(memempty)
      r
    }
  }
  "DoSeq" should "perform DoSeq" in {
    assertResult(Binary(Div, N(1.0), N(0.0))){
      val (_,r) = step(Binary(Seq, N(1.0), Binary(Div, N(1.0), N(0.0))))(memempty)
      r
    }
  }
  "DoArith" should "perform DoArith" in {
    assertResult(N(10)){
      val (_,r) = step(Binary(Div, N(100), N(10)))(memempty)
      r
    }
    assertResult(N(110)){
      val(_,r) = step(Binary(Plus, N(100), N(10)))(memempty)
      r
    }
    assertResult(N(90)){
      val(_,r) = step(Binary(Minus, N(100), N(10)))(memempty)
      r
    }
    assertResult(N(1000)){
      val(_,r) = step(Binary(Times, N(100), N(10)))(memempty)
      r
    }
  }
  "DoPlusString" should "perform DoPlusString" in {
    assertResult(S("hibye")) {
      val(_,r) = step(Binary(Plus, S("hi"), S("bye")))(memempty)
      r
    }
    intercept[StuckError] {
      val(_,r) = step(Binary(Plus, N(10), S("bye")))(memempty)
      r
    }
  }
  "DoInequalityNumber and String" should "perform DoInequalityNumber" in {
    assertResult(B(true)) {
      val(_,r) = step(Binary(Lt, N(12), N(14)))(memempty)
      r
    }
    assertResult(B(false)) {
      val(_,r) = step(Binary(Ge, S("a"), S("b")))(memempty)
      r
    }
  }
  "do equality" should "perform doEquality" in {
    assertResult(B(true)){
      val(_,r) = step(Binary(Eq, Function(None, List(("x", MTyp(MName, TNumber))), None, Binary(Plus, N(1.0), Var("x"))), Function(None, List(("x", MTyp(MName, TNumber))), None, Binary(Plus, N(1.0), Var("x")))))(memempty)
      r
    }
    assertResult(B(false)){
      val(_,r) = step(Binary(Eq, Function(None, List(("y", MTyp(MName, TNumber))), None, Binary(Plus, N(1.0), Var("x"))), Function(None, List(("x", MTyp(MName, TNumber))), None, Binary(Plus, N(1.0), Var("x")))))(memempty)
      r
    }
  }
  "DoDecl" should "perform DoDecl" in {
    assertResult(Binary(Plus, Binary(Div, N(1.0), N(123)), S("g"))) {
      val(_,r) = step(Decl(MName, "g", Binary(Div, N(1.0), N(123)), Binary(Plus, Var("g"), S("g"))))(memempty)
      r
    }
  }
  "DoCall" should "perform DoCall" in {
    val foo = Function(None, List(("x",MTyp(MConst, TBool))), None, Binary(Eq, Var("x"), B(true)))
    assertResult(Binary(Eq, B(false), B(true))){
      val(_,r) = step(Call(foo, List(B(false))))(memempty)
      r
    }
    assertResult(Binary(Eq,B(true),Binary(Plus, N(1.0), Binary(Minus, N(1.0), N(1.0))))){
      val(_,r) = step(Call(Function(None, List(("x",MTyp(MConst, TBool)),("y", MTyp(MName, TNumber))), None, Binary(Eq, Var("x"), Var("y"))), List(B(true), Binary(Plus, N(1.0), Binary(Minus, N(1.0), N(1.0))))))(memempty)
      r
    }
  }
  "DoCallRec" should "perform DoCallRec" in {
    val foo = Function(Some("f"),List(("n",MTyp(MConst,TNumber))),Some(TNumber),If(Binary(Eq,Var("n"),N(0.0)),N(0.0),Call(Var("f"),List(Binary(Minus,N(1.0),N(1.0))))))
    assertResult(If(Binary(Eq, N(1.0), N(0.0)), N(0.0), Call(Function(Some("f"),List(("n",MTyp(MConst,TNumber))),Some(TNumber),If(Binary(Eq,Var("n"),N(0.0)),N(0.0),Call(Var("f"),List(Binary(Minus,N(1.0),N(1.0)))))), List(Binary(Minus, N(1.0), N(1.0)))))) {
      val(_,r) = step(Call(foo, List(N(1.0))))(memempty)
      r
    }
  }
  "DoGetField" should "perform DoGetField" in {
    val obj = Obj(Map("a" -> N(1), "b"-> N(8), "de" -> Function(None, List(), None, N(1.0))))
    assertResult(Function(None,List(),None,N(1.0))){
      val(m,r) = step(GetField(obj, "de"))(memempty)
      val(_,r2) = step(r)(m)
      r2
    }
  }
}

// An adapter class to pass in your Lab5 object.
class Lab5SpecRunner extends Lab5Spec(jsy.student.Lab5)

// The next bit of code runs a test for each .jsy file in src/test/resources/lab5.
// The test expects a corresponding .ans file with the expected result.
class Lab5JsyTests extends JavascriptyTester(None, "lab5", jsy.student.Lab5)

class Lab5Suite extends Suites(
  new Lab5SpecRunner,
  new Lab5JsyTests
)