package interp

trait Lam :
  type Exp[T]
  def lam[A,B](body: Exp[A] => Exp[B]) : Exp[A => B]
  def app[A,B](fun: Exp[A => B], arg: Exp[A]): Exp[B]

trait PCF extends Lam: 
  type Exp[T]
  def num(i : Int): Exp[Int]
  def plus(a: Exp[Int], b: Exp[Int]): Exp[Int]
  def fix[A,B](f:Exp[A=>B]=>Exp[A=>B]): Exp[A=>B]
  def $if[A](cond: Exp[Int], th: => Exp[A], els: => Exp[A]): Exp[A]


trait LamInterp extends Lam :
  type Exp[T] = T 
  def lam[A,B](body: Exp[A] => Exp[B]) = body
  def app[A,B](fun: Exp[A => B], arg: Exp[A]) = fun(arg)


trait PCFInterp extends PCF with LamInterp :
  def num(i : Int) = i
  def plus(a: Exp[Int], b: Exp[Int]) = a + b
  def fix[A,B](f:Exp[A=>B]=>Exp[A=>B]) = {
    def g(x: A): B = f(g)(x)
    g
  }
  def $if[A](cond: Exp[Int], th: => Exp[A], els: => Exp[A]) = 
    if (cond == 0) then th else els

object PCF extends PCFInterp

object PCFPP extends Lam with PCF :
  type Exp[T] = String
  var nest = 0
  def nesting(f: String => String)(x: String) = { 
    nest += 1; try f(x) finally nest -= 1
  }
  def lam[A,B](body: Exp[A] => Exp[B]) = s"lam(${nesting(body)(s"x${nest}")})"
  def app[A,B](fun: Exp[A => B], arg: Exp[A]) = s"app(${fun}, ${arg})"
  def num(i : Int) = i.toString
  def plus(a: Exp[Int], b: Exp[Int]) = s"${a} + ${b}"
  def fix[A,B](f:Exp[A=>B]=>Exp[A=>B]) = s"fix(${nesting(f)(s"x${nest}")})"
  def $if[A](cond: Exp[Int], th: => Exp[A], els: => Exp[A]): Exp[A] = s"if ${cond} then ${th} else ${els}"

/*
Staged version. Doesn't compile due to missing context parameters in places.
Requires changes to the base traits, e.g., type parameters must have
Type as context bound.

import scala.quoted._
object PCFStaged extends Lam with PCF :
  type Exp[T] = (Type[T], Quotes) ?=> Expr[T]
  def lam[A,B](body: Exp[A] => Exp[B]) = '{ (x: A) => ${ body('x) } }
  def app[A,B](fun: Exp[A => B], arg: Exp[A]) = '{ ${fun}($arg) }
  def num(i : Int) = '{ i }
  def plus(a: Exp[Int], b: Exp[Int]) = '{ $a + $b }
  def fix[A,B](f:Exp[A=>B]=>Exp[A=>B])= ???
  def $if[A](cond: Exp[Int], th: => Exp[A], els: => Exp[A]): Exp[A] = 
    '{ if (${cond} == 0) then $th else $els }
*/



/**
 * Generic Lam DSL as an instance of Lam, using context functions.
 * Allows for nicer definitions of generic Lam expressions, which are parametric in
 * the concrete Symantics. 
 * 
 * However, there is a problem below, which is why it is not possible to define
 * it in this self-circular way.
 */
object LamDSLBad extends Lam :
  type Exp[T] = (l : Lam) ?=> l.Exp[T]
  override def lam[A,B](body: Exp[A] => Exp[B]) = 
    (l: Lam) ?=>
    ???
    /**
     * have :
     * l' : Lam (implicit)
     * body : ((l : Lam) ?=> l.Exp[A]) => ((l : Lam) ?=> l.Exp[B])
     * need: 
     * ((l : Lam) ?=> l.Exp[A => B])
     * resp. l'.Exp[A=>B]
     * 
     * problem: body cannot be called without an explicit variable representation, as we need to eta-expand
     * however, it could work with HOAS if we had the type
     *    body : (l : Lam) ?=> (l.Exp[A] => l.Exp[A])      
     */
  override def app[A,B](fun: Exp[A => B], arg: Exp[A]) = (l : Lam) ?=> l.app(fun(using l), arg(using l)) 



def identity = [A] => (l : Lam) ?=> 
  l.lam(x => x)

def ex1(using l : PCF) =
  import l._
  app(lam(x => plus(num(5), x)), num(7))


/**
 * This version fixes the defect we encountered in LamDSLBad.
 * But we will see that we just shifted the problem...
 */
trait Lam2 :
  type ~>[-A,+B] //we abstract over the arrow type
  type Exp[+T]
  def lam[A,B](body: A ~> B) : Exp[A => B]
  def app[A,B](fun: Exp[A => B], arg: Exp[A]): Exp[B]

trait PCF2 extends Lam2:
  def num(i : Int): Exp[Int]
  def plus(a: Exp[Int], b: Exp[Int]): Exp[Int]
  def fix[A,B](f:(A=>B) ~> (A=>B)): Exp[A=>B]
  def $if[A](cond: Exp[Int], th: => Exp[A], els: => Exp[A]): Exp[A]

trait Lam2DSL extends Lam2 :
  type Ctx <: Lam2 
  type Exp[+T] = (l : Ctx) ?=> l.Exp[T]
  type ~>[-A,+B] = (l : Ctx) ?=> (l.~>[A, B]) //now we can properly thread the implicit context
  def lam[A,B](body: A ~> B) : Exp[A => B] = (l: Ctx) ?=> l.lam(body(using l))
  def app[A,B](fun: Exp[A => B], arg: Exp[A]): Exp[B] = (l : Ctx) ?=> l.app(fun(using l), arg(using l))


trait PCF2DSL extends Lam2DSL with PCF2 :
  type Ctx <: Lam2 with PCF2 
  def num(i : Int): Exp[Int] = (c : Ctx) ?=> c.num(i)
  def plus(a: Exp[Int], b: Exp[Int]): Exp[Int] = (c : Ctx) ?=> c.plus(a(using c), b(using c)) 
  def fix[A,B](f:(A=>B) ~> (A=>B)): Exp[A=>B] = (c : Ctx) ?=> c.fix(f(using c)) 
  def $if[A](cond: Exp[Int], th: => Exp[A], els: => Exp[A]): Exp[A] = 
    (c : Ctx) ?=> c.$if(cond(using c), th(using c), els(using c))

object Frontend extends PCF2DSL :
  type Ctx = Lam2 with PCF2 

object Tests :
  import Frontend._

  /**
   * Problem: since the concrete ~> is not known, clients cannot supply lambdas
   */
  //def id[A] : Exp[A => A] = lam((x : Exp[A]) => x)
  //def x() : Exp[Int] = $if[Int](num(10), plus(num(0), num(1)), num(12))



