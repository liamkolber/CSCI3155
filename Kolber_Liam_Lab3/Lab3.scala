package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._
  
  /*
   * CSCI 3155: Lab 3 
   * Liam Kolber
   * 
   * Partner: Kylee Bennett
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case Undefined => Double.NaN
      case N(n)      => n
      case B(b)      => if (b) 1.0 else 0.0
      case S(s)      => try s.toDouble catch {case _: Throwable => Double.NaN}
      case Function(_, _, _) => Double.NaN
      case _         => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case Undefined => false
      case N(n)      => if (n == 0.0 || n == -0.0 || n.isNaN) false else true
      case B(b)      => b
      case S(s)      => if (s == "") false else true
      case Function(_, _, _) => true
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case Undefined => "undefined"
      case N(n)      => prettyNumber(n)
      case B(b)      => b.toString
      case S(s)      => s
      case Function(_, _, _) => "function"
    }
  }

  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case _ =>
        val (n1, n2) = (toNumber(v1), toNumber(v2))
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }

  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e

      /* Inductive Cases */
      case Unary(Neg,e1)        => N(-toNumber(eval(env, e1)))
      case Unary(Not,e1)        => B(!toBoolean(eval(env, e1)))

      case Binary(And,e1,e2)    =>
        val eval1 = eval(env,e1)
        if (toBoolean(eval1)) eval(env,e2) else eval1
      case Binary(Or,e1,e2)     =>
        val eval1 = eval(env,e1)
        if (toBoolean(eval1)) eval1 else eval(env,e2)


      case Binary(Plus,e1,e2)   =>
        val eval1 = eval(env,e1)
        val eval2 = eval(env,e2)
        (eval1,eval2) match {
          case (S(_),_) | (_,S(_))  => S(toStr(eval1) + toStr(eval2))
          case (_,_)                => N(toNumber(eval1) + toNumber(eval2))
        }
      case Binary(Minus,e1,e2)  => N(toNumber(eval(env, e1)) - toNumber(eval(env, e2)))
      case Binary(Times,e1,e2)  => N(toNumber(eval(env, e1)) * toNumber(eval(env, e2)))
      case Binary(Div,e1,e2)    => N(toNumber(eval(env, e1)) / toNumber(eval(env, e2)))

      case Binary(bop @(Eq | Ne), e1, e2) =>
        val v1 = eval(env,e1)
        val v2 = eval(env,e2)
        require(isValue(v1))
        require(isValue(v2))
        (v1, v2) match {
          case (Function(_,_,_),_) => throw DynamicTypeError(v1)
          case (_,Function(_,_,_)) => throw DynamicTypeError(v2)
          case _ =>
            (bop: @unchecked) match {
              case Eq => B(v1 == v2)
              case Ne => B(v1 != v2)
            }
        }

      case Binary(bop @ (Lt|Le|Gt|Ge), e1, e2) => B(inequalityVal(bop, eval(env,e1), eval(env,e2)))

      case Print(e1)            => println(pretty(eval(env, e1))); Undefined
      case Binary(Seq,e1,e2)    => eval(env,e1); eval(env,e2)
      case If(e1,e2,e3)         => if (toBoolean(eval(env,e1))) eval(env,e2) else eval(env,e3)
      case Var(x)               => lookup(env, x)
      case ConstDecl(x,e1,e2)   => eval(extend(env,x,eval(env,e1)),e2)

      case Call(e1, e2) =>
        val eval1 = eval(env,e1)
        eval1 match {
          case Function(None, x, y)     => eval(extend(env, x, eval(env,e2)), y)
          case Function(Some(f), x, y)  => eval(extend(extend(env, f, eval1), x, eval(env, e2)), y)
          case _                        => throw DynamicTypeError(e)
      }
    }
  }

  /* Small-Step Interpreter with Static Scoping */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e,n) match {
      case None     => e
      case Some(e1) => loop(e1,n+1)
    }
    loop(e0, 0)
  }
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    e match {
      case Var(y)               => if (x == y) v else Var(y)
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1)            => Print(substitute(e1, v, x))
      case Function(p, y, e1)   => p match {
        case None               => if (x == y) e else Function(p, y, substitute(e1, v, x)) //Case if variable x equals y
        case Some(f)            => if (x == f || x == y) e else Function(Some(f), y, substitute(e1, v, x))
      }
      case Binary(bop, e1, e2)  => Binary(bop, substitute(e1, v, x), substitute(e2, v, x))
      case Unary(uop, e1)       => Unary(uop, substitute(e1, v, x))
      case If(e1, e2, e3)       => If(substitute(e1, v, x), substitute(e2, v, x), substitute(e3, v, x))
      case ConstDecl(y, e1, e2) => if (x == y) ConstDecl(y, substitute(e1, v, x), e2) else ConstDecl(y, substitute(e1, v, x), substitute(e2, v, x))

      case Call(e1, e2)         => Call(substitute(e1, v, x), substitute(e2, v, x))
    }
  }

  def step(e: Expr): Expr = {
    e match {
        //DoPrint
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
        //DoNeg
      case Unary(Neg,v1) if isValue(v1) => N(-toNumber(v1))
        //DoNot
      case Unary(Not,v1) if isValue(v1) => B(!toBoolean(v1))
        //DoSeq
      case Binary(Seq,v1,e2) if isValue(v1) => e2
        //DoPlusNumber, DoPlusString1, DoPlusString2
      case Binary(Plus,v1,e2) if isValue(v1) && isValue(e2) => (v1,e2) match {
        case (S(s1),v2) => S(s1+toStr(v2))
        case (v2,S(s2)) => S(toStr(v2)+s2)
        case (_,_) => N(toNumber(v1)+toNumber(e2))
      }
        //DoArith
      case Binary(Minus,v1,v2) if isValue(v1) && isValue(v2) => N(toNumber(v1)-toNumber(v2))
      case Binary(Times,v1,v2) if isValue(v1) && isValue(v2) => N(toNumber(v1)*toNumber(v2))
      case Binary(Div,v1,v2) if isValue(v1) && isValue(v2)  => N(toNumber(v1)/toNumber(v2))

        //DoInequalityNumber1, DoInequalityNumber2, DoInequalityString
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(bop, v1,v2))
        //DoEquality
      case Binary(bop @(Eq | Ne), v1, v2) if isValue(v1) && isValue(v2)=>
        (v1, v2) match {
          case (Function(_,_,_),_) => throw DynamicTypeError(v1)
          case (_,Function(_,_,_)) => throw DynamicTypeError(v2)
          case _ =>
            (bop: @unchecked) match {
              case Eq => B(v1 == v2)
              case Ne => B(v1 != v2)
            }
        }

        //DoAndTrue, DoAndFalse
      case Binary(And,v1,e2) if isValue(v1)=> if (toBoolean(v1)) e2 else v1
        //DoOrTrue, DoOrFalse
      case Binary(Or, v1, e2) if isValue(v1) => if (toBoolean(v1)) v1 else e2

        //DoIfTrue, DoIfFalse
      case If(v1,e2,e3) if isValue(v1) => if (toBoolean(v1)) e2 else e3
        //DoConst
      case ConstDecl(x1, v1, e2) if isValue(v1) => substitute(e2,v1,x1)
        //DoCall, DoCallRec
      case Call(v1, v2) if isValue(v1) && isValue(v2) => v1 match{
        case Function(None, x1, e1) => substitute(e1, v2, x1)
        case Function(Some(f), x1, e1) => substitute(substitute(e1, v2, x1), v1, f)
        case _ => throw DynamicTypeError(e)
      }

      /* Inductive Cases: Search Rules */
        //SearchPrint
      case Print(e1) => Print(step(e1))
        //SearchUnary
      case Unary(uop,e1) => Unary(uop,step(e1))
        //SearchEquality, SearchBinaryArith
      case Binary(bop, v1, e2) if isValue(v1) => bop match {
        case (Plus|Minus|Times|Div|Lt|Le|Gt|Ge) => Binary(bop, v1, step(e2))
        case (Eq|Ne) => v1 match {
          case Function(_, _, _) => throw DynamicTypeError(e)
          case _ => Binary(bop, v1, step(e2))
        }
      }
        //SearchBinary
      case Binary(bop,e1,e2) => Binary(bop,step(e1),e2)
        //SearchIf
      case If(e1,e2,e3) => If(step(e1),e2,e3)
        //SearchConst
      case ConstDecl(x,e1,e2) => ConstDecl(x,step(e1),e2)
        //SearchCall1
      case Call(e1, e2) if !isValue(e1) => Call(step(e1), e2)
        //SearchCall2
      case Call(Function(p, x, e1), e2) => Call(Function(p,x,e1), step(e2))
        //TypeErrorCall
      case Call(v1,_) if isValue(v1) => throw DynamicTypeError(e)

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }

  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}
