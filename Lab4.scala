package jsy.student

import jsy.lab4.Lab4Like

object Lab4 extends jsy.util.JsyApplication with Lab4Like {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * <Bryan Heiser>
   * 
   * Partner: <Brad Smith>
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
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /* Collections and Higher-Order Functions */
  
  /* Lists */
  
  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => l
    case h1 :: (t1 @ (h2 :: _)) => if (h1==h2) compressRec(t1) else h1 :: compressRec(t1)
  }
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => (h, acc) match {
      case (h1, Nil) => h1 :: Nil
      case (h1, t1 @ (h2 :: _)) => if (h1==h2) t1 else h1 :: t1
    }
  }
  
  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => Nil
    case h :: t => f(h) match {
      case None => h :: mapFirst(t)(f)
      case Some(thing) => thing :: t
    }
  }
  
  /* Trees */

  def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
    def loop(acc: A, t: Tree): A = t match {
      case Empty => acc
      case Node(l, d, r) => f(loop(loop(acc, l), r),d)
    }
    loop(z, t)
  }

  // An example use of foldLeft
  def sum(t: Tree): Int = foldLeft(t)(0){ (acc, d) => acc + d }

  // Create a tree from a list. An example use of the
  // List.foldLeft method.
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }

  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = foldLeft(t)((true, None: Option[Int])){
      (acc:(Boolean, Option[Int]), c: Int) => (acc, c) match {
        case ((true, None), curr) => (true, Some(curr))
        case ((true, Some(prev)), curr) => if (curr < prev) (true, Some(curr)) else (false, Some(curr))
        case ((false, _), curr) => (false, Some(curr))
      }
    }
    b
  }

  /* Type Inference */

  // While this helper function is completely given, this function is
  // worth studying to see how library methods are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }
  
  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typeof(env, e1); TUndefined
      case N(_) => N(_); TNumber
      case B(_) => B(_); TBool
      case Undefined => Undefined; TUndefined
      case S(_) => S(_); TString
      case Var(x) => Var(x); env(x)
      case Decl(mode, x, e1, e2) => extend(env, x, typeof(env, e1)); typeof(env, e2)
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typeof(env, e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TString, TString) => TString
        case (TNumber, TNumber) => TNumber
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e2)

      }
      case Binary(Minus|Times|Div, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber ) => TNumber
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e2)
      }
      case Binary(Eq|Ne, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TBool
        case (TString, TString) => TBool
        case (TBool, TBool) => TBool
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e2)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TString, TString) => TBool
        case (TNumber, TNumber) => TBool
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e2)
      }
      case Binary(And|Or, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TBool, TBool) => TBool
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e2)
      }
      case Binary(Seq, e1, e2) => typeof(env, e2)

      case If(e1, e2, e3) => typeof(env, e1) match {
        case TBool => (typeof(env, e2), typeof(env, e3)) match {
          case (TNumber, TNumber) => TNumber
          case (TString, TString) => TString
          case (TBool, TBool) => TBool
          case (tgot, _) => err(tgot, e1)
          case (_, tgot) => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          /***** Add cases here *****/
          case (Some(f), Some(returnT)) => env + (f -> TFunction(params, returnT))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = params.foldLeft(env1){
          case (acc, (s, MTyp(m, t))) => acc + (s -> t)
        }
        // Infer the type of the function body
        val t1 = typeof(env2, e1)
        // Check with the possibly annotated return type
        tann match {
          case None => TFunction(params, t1)
          case Some(t) => if (t1==t) TFunction(params, t1) else err(t1, e1)
         }
      }
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params zip args).foreach {
            case ((str, MTyp(m, t)), ar) => if (typeof(env, ar)==t) t else err(typeof(env, ar), ar)
          };
          tret
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => TObj(fields.mapValues((e1)=>typeof(env, e1)))
      case GetField(e1, f) => typeof(env, e1) match {
        case TObj(mapf) => mapf.get(f) match {
          case Some(t) => t
          case None => err(typeof(env, e1), e1)
        }
        case tgot => err(tgot, e1)
      }
    }
  }
  
  
  /* Small-Step Interpreter */

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => bop match {
        case Lt => s1 < s2
        case Le => s1 <= s2
        case Gt => s1 > s2
        case Ge => s1 >= s2
      }
      case (N(n1), N(n2)) => bop match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }

  /* This should be the same code as from Lab 3 */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e, n) match {
      case None => e
      case Some(e1) => loop(e1, n+1)
    }
    loop(e0, 0)
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, esub, x))
        /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, substitute(e1, esub, x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1, esub, x), substitute(e2, esub, x))
      case If(e1, e2, e3) => If(substitute(e1, esub, x), substitute(e2, esub, x), substitute(e3, esub, x))
      case Var(y) => if (y==x) esub else Var(y)
      case Decl(mode, y, e1, e2) => if (y==x) Decl(mode, y, substitute(e1, esub, x), e2) else Decl(mode, y, substitute(e1, esub, x), substitute(e2, esub, x))
        /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) => p match {
        case None =>
          val b = params.foldLeft(false) {
            case (s, mt) => s == x
          }
          if (b) e else Function(p, params, tann, substitute(e1, esub, x))
        case Some(name) => if (name==x) e else {
          val b = params.foldLeft(false){
            case (s, mt) => s == x
          }
          if (b) e else Function(p, params, tann, substitute(e1, esub, x))
        }
      }
      case Call(e1, args) =>
        val b = args.foldLeft(false){
          case s => s == x
        }
        if (b) Call(substitute(e1, esub, x), args) else Call(substitute(e1, esub, x), args.map((exp) => substitute(exp, esub, x)))
        // Call(substitute(e1, esub, x), args.foldLeft(List(): List[Expr]){
          //        case (acc, exp) => acc + substitute(exp, esub, x)
          //      })
        /***** New cases for Lab 4 */
      case Obj(fields) => Obj(fields.mapValues((e1)=>substitute(e1, esub, x)))
      case GetField(e1, f) => GetField(substitute(e1, esub, x), f)
    }

    val fvs = freeVars(esub)
    def fresh(x: String): String = if (fvs.contains(x)) fresh(x + "$") else x
    subst(rename(e)(fresh))
  }

  /* Rename bound variables in e */
  def rename(e: Expr)(fresh: String => String): Expr = {
    def ren(env: Map[String,String], e: Expr): Expr = {
      e match {
        case N(_) | B(_) | Undefined | S(_) => e
        case Print(e1) => Print(ren(env, e1))

        case Unary(uop, e1) => Unary(uop, ren(env, e1))
        case Binary(bop, e1, e2) => Binary(bop, ren(env, e1), ren(env, e2))
        case If(e1, e2, e3) => If(ren(env, e1), ren(env, e2), ren(env, e3))

        case Var(y) =>
          if (env.contains(y)) Var(env(y)) else e //env(y) returns a string
        case Decl(mode, y, e1, e2) =>
          val yp = fresh(y)
          Decl(mode, yp, ren(env, e1), ren(env + (y -> yp), e2))

        case Function(p, params, rettyp, e1) => {
          val (pp, envp): (Option[String], Map[String,String]) = p match {
            case None => (None, env)
            case Some(x) => {
              val pp = fresh(x)
              (Some(pp), extend(env, x, pp))
            }
          }
          val (paramsp, envpp) = params.foldRight( (Nil: List[(String,MTyp)], envp) ) {
            case ((s,t), (parameters, env1)) => {
              val pfresh = fresh(s)
              ((pfresh, t) :: parameters, extend(env1, s, pfresh))
            }
          }
          Function(pp, paramsp, rettyp, ren(envpp, e1))
        }

        case Call(e1, args) => ???

        case Obj(fields) => ???
        case GetField(e1, f) => ???
      }
    }
    ren(empty, e)
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case MConst => if (isValue(e)) false else true
    case MName => false
  }

  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined //DoPrint
        /***** Cases needing adapting from Lab 3. */
        //DoNeg
      case Unary(Neg, v1) if isValue(v1) => v1 match {
        case N(n) => N(-n)
      }
        /***** More cases here */
        //DoNot
      case Unary(Not, v1) if isValue(v1) => v1 match {
        case B(b) => if (b) B(false) else B(true)
      }
        //DoSeq
      case Binary(Seq, v1, e2) if isValue(v1) => e2

        //DoPlusString and DoArith (only Plus)
      case Binary(Plus, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (N(n1), N(n2)) => N(n1 + n2)
        case (S(s1), S(s2)) => S(s1 + s2)
      }
        //rest of DoArith
      case Binary(Minus, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (N(n1), N(n2)) => N(n1 - n2)
      }
      case Binary(Times, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (N(n1), N(n2)) => N(n1 * n2)
      }
      case Binary(Div, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (N(n1), N(n2)) => N(n1 / n2)
      }
        //DoAndTrue and DoAndFalse
      case Binary(And, v1, e2) if isValue(v1) => v1 match {
        case B(b) => if (b) e2 else v1
      }
        //DoOrTrue and DoOrFalse
      case Binary(Or, v1, e2) if isValue(v1) => v1 match {
        case B(b) => if (b) v1 else e2
      }
        //DoInequalityNumber, DoInequalityString, and DoEquality
      case Binary(bop, v1, v2) if isValue(v1) && isValue(v2) => bop match {
        case Lt | Le | Gt | Ge => B(inequalityVal(bop, v1, v2))
        case Eq | Ne => if (bop==Eq) B(v1==v2) else B(v1!=v2)
      }
        //DoIfTrue and DoIfFalse
      case If(v1, e2, e3) if isValue(v1) => v1 match {
        case B(b) => if (b) e2 else e3
      }
        //DoDecl
      case Decl(m, x, e1, e2) if !isRedex(m, e1) => substitute(e2, e1, x)
        //DoCall, DoCallRec, and SearchCall2
      case Call(v1, args) if isValue(v1) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val pazip = params zip args
            if (pazip.forall(p => !isRedex(p._1._2.m,p._2))) {
              val e1p = pazip.foldRight(e1) {
                case (pa, exp) => substitute(exp, pa._2, pa._1._1)
              }
              p match {
                case None => e1p
                case Some(x1) => substitute(e1p, v1, x1)
              }
            }
            else {
              val pazipp = mapFirst(pazip) {
                case (t1 @ (s, MTyp(m, t)), exp) => if (isRedex(m, exp)) Some(t1, step(exp)) else None
              }
              Call(v1, pazipp.unzip._2)
            }
          }
          case _ => throw StuckError(e)
        }
        /***** New cases for Lab 4. */
      case GetField(v1, f) if isValue(v1) => v1 match {
        case Obj(fields) => fields.get(f).get
      }

      /* Inductive Cases: Search Rules */
        //SearchPrint
      case Print(e1) => Print(step(e1))
        /***** Cases from Lab 3. */
        //SearchUnary
      case Unary(uop, e1) => Unary(uop, step(e1))
        /***** More cases here */
        //SearchBinary2
      case Binary(bop, v1, e2) if isValue(v1) => Binary(bop, v1, step(e2))
        //SearchBinary1
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)
        //SearchIf
      case If(e1, e2, e3) => If(step(e1), e2, e3)
        //SearchDecl
      case Decl(m, x, e1, e2) if isRedex(m, e1) => Decl(m, x, step(e1), e2)
        /***** Cases needing adapting from Lab 3 */
      case Call(v1 @ Function(_, _, _, _), args) => Call(v1, mapFirst(args){
        case exp => if (isValue(exp)) Some(exp) else Some(step(exp))
      })
      case Call(e1, args) => Call(step(e1), args)
        /***** New cases for Lab 4. */

      case Obj(fields) =>
        Obj(mapFirst(fields.toList){
          case (str, exp) => if (isValue(exp)) None else Some(str,step(exp))
        }.toMap)

      case GetField(e1, f) => GetField(step(e1), f)
      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => throw StuckError(e)
    }
  }
  
  
  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}

