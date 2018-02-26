package jsy.student
import jsy.lab3.Lab3Like
import jsy.lab3.Parser.parse
import jsy.lab3.ast._
import jsy.tester.JavascriptyTester
import org.scalatest._
class Lab3Spec(lab3: Lab3Like) extends FlatSpec {
  import lab3._
  "eval/function" should "be considered values" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Var(x))
    val e2 = Function(Some(f), x, Var(x))
    assert(evaluate(e1) == e1)
    assert(evaluate(e2) == e2)
  }
  "eval/call" should "evaluate a function using big-step semantics" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Binary(Plus, Var(x), N(1)))
    val e2 = N(2)
    val e3 = evaluate(Call(e1, e2))
    assert(e3 === N(3))
  }
  it should "handle recursive functions using big-step semantics" in {
    val f = "f"
    val x = "x"
    val fbody = If(Binary(Eq, Var(x), N(0)), Var(x), Binary(Plus, Var(x), Call(Var(f), Binary(Minus, Var(x), N(1)))))
    val e1 = Function(Some(f), x, fbody)
    val e2 = N(3)
    val e3 = evaluate(Call(e1, e2))
    assert(e3 === N(6))
  }
  "step/call" should "evaluate a function using small-step semantics" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Binary(Plus, Var(x), N(1)))
    val e2 = N(2)
    val e3 = iterateStep(Call(e1, e2))
    assert(e3 === N(3))
  }
  it should "handle recursive functions using small-step semantics" in {
    val f = "f"
    val x = "x"
    val fbody = If(Binary(Eq, Var(x), N(0)), Var(x), Binary(Plus, Var(x), Call(Var(f), Binary(Minus, Var(x), N(1)))))
    val e1 = Function(Some(f), x, fbody)
    val e2 = N(3)
    val e3 = iterateStep(Call(e1, e2))
    assert(e3 === N(6))
  }
  "substitute" should "perform syntatic substitution respecting shadowing" in {
    val xplus1 = parse("x + 1")
    val twoplus1 = parse("2 + 1")
    assert(substitute(xplus1, N(2), "x") === twoplus1)
    val constx3 = parse("const x = 3; x")
    val shadowx = Binary(Plus, constx3, Var("x"))
    assert(substitute(shadowx, N(2), "x") === Binary(Plus, constx3, N(2)))
  }
  {
    val one = parse("1")
    "iterate" should "stop if the callback body returns None" in {
      assertResult(one) {
        iterate(one) { (_, _) => None }
      }
    }
    it should "increment the loop counter on each iteration and use e if the callback body returns Some(e)" in {
      assertResult(parse("--1")) {
        iterate(one) { (e: Expr, n: Int) =>
          if (n == 2) None else Some(Unary(Neg, e))
        }
      }
    }
  }
  /* Tests based on rules */
  {
    val xval = N(2)
    val envx = extend(empty, "x", xval)
    val varx = Var("x")
    val e1 = parse("2 - 1 - 1")
    val e1p = parse("1 - 1")
    val e2 = parse("3 - 1 - 1")
    val e2p = parse("2 - 1")
    val e3 = parse("3*2+1")
    val v1 = N(0)
    val v2 = N(1)
    val str1 = S("hello")
    val str2 = S("world")
    val vidfunction = parse("function (x) { return x }")
    "EvalVar" should "perform EvalVar" in {
      assertResult(xval) {
        eval(envx, varx)
      }
    }
    "EvalNeg" should "perform EvalNeg" in {
      val np = -toNumber(v1)
      assertResult(N(np)) {
        eval(envx, Unary(Neg, e1))
      }
    }
    "EvalTypeErrorEquality" should "perform EvalTypeErrorEquality1" in {
      intercept[DynamicTypeError] {
        eval(envx, Binary(Eq, vidfunction, e2))
      }
    }
    it should "perform EvalTypeErrorEquality2" in {
      intercept[DynamicTypeError] {
        eval(envx, Binary(Eq, e1, vidfunction))
      }
    }
    "EvalTypeErrorCall" should "perform EvalTypeErrorCall" in {
      intercept[DynamicTypeError] {
        eval(envx, Call(v1, e2))
      }
    }
    "DoNeg" should "perform DoNeg" in {
      val np = -toNumber(v1)
      assertResult(N(np)) {
        step(Unary(Neg, v1))
      }
    }
    "DoNot" should "perform DoNot" in {
      val bp = !toBoolean(v1)
      assertResult(B(bp)) {
        step(Unary(Not, v1))
      }
    }
    "DoSeq" should "perform DoSeq" in {
      assertResult(e2) {
        step(Binary(Seq, v1, e2))
      }
    }
    "DoPlusNumber" should "perform DoPlusNumber" in {
      val np = toNumber(v1) + toNumber(v2)
      assertResult(N(np)) {
        step(Binary(Plus, v1, v2))
      }
    }
    "DoPlusString" should "perform DoPlusString1" in {
      val strp = toStr(str1) + toStr(v2)
      assertResult(S(strp)) {
        step(Binary(Plus, str1, v2))
      }
    }
    it should "perform DoPlusString2" in {
      val strp = toStr(v1) + toStr(str2)
      assertResult(S(strp)) {
        step(Binary(Plus, v1, str2))
      }
    }
    "DoArith" should "perform DoArith" in {
      List(
        ((x:Double, y:Double)=> x - y, Minus),
        ((x:Double, y:Double)=> x * y, Times),
        ((x:Double, y:Double)=> x / y, Div)
      ).foreach((t)=>{
        val (f, bop) = t
        val np = f(toNumber(v1), toNumber(v2))
        assertResult(N(np)) {
          step(Binary(bop, v1, v2))
        }
      })
    }
    "DoInequalityNumber" should "perform DoInequalityNumber" in {
      List(
        ((x:Double, y:Double)=> x <  y, Lt),
        ((x:Double, y:Double)=> x <= y, Le),
        ((x:Double, y:Double)=> x >  y, Gt),
        ((x:Double, y:Double)=> x >= y, Ge)
      ).foreach((t)=>{
        val (f, bop) = t
        val bp = f(toNumber(v1), toNumber(v2))
        assertResult(B(bp)) {
          step(Binary(bop, v1, v2))
        }
      })
    }
    "DoInequalityString" should "perform DoInequalityString" in {
      List(
        ((x:String, y:String)=> x <  y, Lt),
        ((x:String, y:String)=> x <= y, Le),
        ((x:String, y:String)=> x >  y, Gt),
        ((x:String, y:String)=> x >= y, Ge)
      ).foreach((t)=>{
        val (f, bop) = t
        val bp = f(toStr(str1), toStr(str2))
        assertResult(B(bp)) {
          step(Binary(bop, str1, str2))
        }
      })
    }
    "DoEquality" should "perform DoEquality" in {
      List(
        ((x:Expr, y:Expr)=> x == y, Eq),
        ((x:Expr, y:Expr)=> x != y, Ne)
      ).foreach((t) => {
        val (f, bop) = t
        val bp = f(v1, v2)
        assertResult(B(bp)) {
          step(Binary(bop, v1, v2))
        }
      })
    }
    "DoAndTrue" should "perform DoAndTrue" in {
      List(N(1), S(" "), B(true)).foreach((v1)=>{
        assertResult(e2) {
          step(Binary(And, v1, e2))
        }
      })
    }
    "DoAndFalse" should "perform DoAndFalse" in {
      List(N(0), S(""), B(false)).foreach((v1)=>{
        assertResult(v1) {
          step(Binary(And, v1, e2))
        }
      })
    }
    "DoOrTrue" should "perform DoOrTrue" in {
      List(N(1), S(" "), B(true)).foreach((v1)=>{
        assertResult(v1) {
          step(Binary(Or, v1, e2))
        }
      })
    }
    "DoOrFalse" should "perform DoOrfalse" in {
      List(N(0), S(""), B(false)).foreach((v1)=>{
        assertResult(e2) {
          step(Binary(Or, v1, e2))
        }
      })
    }
    "DoIfTrue" should "perform DoIfTrue" in {
      List(N(1), S(" "), B(true)).foreach((v1)=>{
        assertResult(e2) {
          step(If(v1, e2, e3))
        }
      })
    }
    "DoIfFalse" should "perform DoIfFalse" in {
      List(N(0), S(""), B(false)).foreach((v1)=>{
        assertResult(e3) {
          step(If(v1, e2, e3))
        }
      })
    }
    "DoCall" should "perform DoCall" in {
    }
    "DoCallRec" should "perform DoCallRec" in {
      val x1 = "f"
      val x2 = "x"
      val e1 = If(Binary(Eq, Var("x"), N(0)), N(1), Binary(Plus,N(1),Call(Var("f"), Binary(Plus, Var("x"), N(1)))))
      val v1 = Function(Some(x1), x2, e1)
      assertResult(substitute(substitute(e1, v1, x1), v2, x2)) {
        step(Call(v1, v2))
      }
    }
    "SearchUnary" should "perform SearchUnary" in {
      List(Neg, Not).foreach((uop) => {
        assertResult(Unary(uop, e1p)) {
          step(Unary(uop, e1))
        }
      })
    }
    "SearchBinary" should "perform SearchBinary" in {
      List(
        Plus, Minus, Times, Div,
        Eq, Ne,
        Lt, Le, Gt,Ge,
        And, Or,
        Seq
      ).foreach((bop) => {
        assertResult(Binary(bop, e1p, e2)) {
          step(Binary(bop, e1, e2))
        }
      })
    }
    "SearchBinaryArith" should "perform SearchBinaryArith" in {
      List(
        Plus, Minus, Times, Div,
        Lt, Le, Gt, Ge
      ).foreach((bop) => {
        assertResult(Binary(bop, v1, e2p)) {
          step(Binary(bop, v1, e2))
        }
      })
    }
    "SearchEquality" should "perform SearchEquality" in {
      List(Eq, Ne).foreach((bop) => {
        assertResult(Binary(bop, v1, e2p)) {
          step(Binary(bop, v1, e2))
        }
      })
    }
    "TypeErrorEquality" should "perform TypeErrorEquality" in {
      List(Eq, Ne).foreach((bop) => {
        intercept[DynamicTypeError] {
          step(Binary(bop, vidfunction, e2))
        }
        intercept[DynamicTypeError] {
          step(Binary(bop, v1, vidfunction))
        }
      })
    }
    "SearchPrint" should "perform SearchPrint" in {
      assertResult(Print(e1p)) {
        step(Print(e1))
      }
    }
    "SearchIf" should "perform SearchIf" in {
      assertResult(If(e1p, e2, e3)) {
        step(If(e1, e2, e3))
      }
    }
    "SearchConst" should "perform SearchConst" in {
      assertResult(ConstDecl("x", e1p, e2)) {
        step(ConstDecl("x", e1, e2))
      }
    }
    "SearchCall" should "perform SearchCall1" in {
      assertResult(Call(e1p, e2)) {
        step(Call(e1, e2))
      }
    }
    it should "perform SearchCall2" in {
      assertResult(Call(vidfunction, e2p)) {
        step(Call(vidfunction, e2))
      }
    }
    "TypeErrorCall" should "perform TypeErrorCall" in {
      intercept[DynamicTypeError] {
        step(Call(v1, e2))
      }
    }
  }
}
// An adapter class to pass in your Lab3 object.
class Lab3SpecRunner extends Lab3Spec(Lab3)
// The next bit of code runs a test for each .jsy file in src/test/resources/lab3.
// The test expects a corresponding .ans file with the expected result.
class Lab3JsyTests extends JavascriptyTester(None, "lab3", Lab3)
class Lab3Suite extends Suites(
  new Lab3SpecRunner,
  new Lab3JsyTests
)