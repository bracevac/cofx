package interp

import scala.language.postfixOps
import scala.compiletime.ops.int._

trait CoEffScalar[C] :
  def use : C
  def ign : C
  def add(x : C, y: C): C
  def mul(x : C, y: C): C
  def leq(x : C, y: C): Boolean
  extension (c : C)
    infix def ⊕(that : C): C = add(c,that)
    infix def ⊗(that : C): C = mul(c,that) 
    infix def ≤(that : C): Boolean = leq(c,that)

given [C : CoEffScalar] : PreOrder[C] with
   extension (x : C)
     def ≤(that : C) = x ≤ that

given MonoidPlus[C](using cs : CoEffScalar[C]) : Monoid[C] with
   def unit = cs.ign
   extension (x : C)
     def ++(that : C) = x ⊕ that

given MonoidTimes[C](using cs : CoEffScalar[C]) : Monoid[C] with
   def unit = cs.use
   extension (x : C)
     def ++(that : C) = x ⊗ that

given BoundedReuseSc : CoEffScalar[Int] with
  def use = 1
  def ign = 0
  def add(x : Int, that : Int) = x + that
  def mul(x : Int, that : Int) = x * that
  def leq(x : Int, that : Int) = x <= that

given DataflowSc : CoEffScalar[Int] with
  def use = 0
  def ign = 0 
  def add(x : Int, that : Int) = x max that
  def mul(x : Int, that : Int) = x + that
  def leq(x : Int, that : Int) = x <= that

object Liveness :
  enum Lv :
    case D
    case L
    infix def ⊓(that : Lv): Lv = (this,that) match
      case (L, L) => L
      case _      => D
    infix def ⊔(that : Lv): Lv = (this,that) match
      case (D, D) => D
      case _      => L
    infix def ⊑(that : Lv): Boolean = (this,that) match
      case (D,L) | (L,L) | (D,D) => true
      case _ => false

//TODO could the typeclass derivation be utilized here?
given LivenessSc : CoEffScalar[Liveness.Lv] with
  import Liveness._
  import Lv._
  def use = L
  def ign = D
  def add(x : Lv, that : Lv) = x ⊔ that
  def mul(x : Lv, that : Lv) = x ⊓ that
  def leq(x : Lv, that : Lv) = x ⊑ that

trait CoEffShape[S] :
  type zero <: S
  def zero : zero
  type unit <: S
  def unit : unit
  //def ctx_shape[T <: Tuple] : S //TODO needs refinement
  type ⟐[s1 <: S, s2 <: S] <: S
  extension [s1 <: S, s2 <: S](s1 : s1)
    inline def ⟐(s2 : s2): (s1 ⟐ s2)

trait CoEffShapeSplit[S] extends CoEffShape[S] :
  def split[s1 <: S, s2 <: S](s1s2 : s1 ⟐ s2): s1 | s2

/*
given [S : CoEffShape] : Monoid[S] with
  def unit = summon[CoEffShape[S]].zero
  extension (x : S)
     inline def ++(that : S) = x ⟐ that //TODO this won't work, because we have to make ⟐ inline
*/

given FlatShape : CoEffShape[Unit] with
  type zero = Unit
  def  zero = ()
  type unit = Unit
  def  unit = ()
  type ⟐[s1 <: Unit, s2 <: Unit] = Unit
  extension [s1 <: Unit, s2 <: Unit](s1 : s1)
    inline def ⟐(s2 : s2): (s1 ⟐ s2) = ()

given StructShape : CoEffShape[Int] with //TODO better have peano number type resp. non-negative ints? 
  type zero = 0
  def  zero = 0
  type unit = 1
  def  unit = 1
  type ⟐[s1 <: Int, s2 <: Int] = s1 + s2
  extension [s1 <: Int, s2 <: Int](s1 : s1)
    inline def ⟐(s2 : s2): (s1 ⟐ s2) = valueOf[s1 ⟐ s2]

/*given TupleShape : CoEffShape[Tuple] with //TODO: how to generalize to heterogeneous tuple types? 
  type zero = EmptyTuple
  def zero  = Tuple()*/

trait CoEffAlgebra[C, S](using val C : CoEffScalar[C], val S : CoEffShape[S]) :
  type Vec[s <: S]
  inline def unit(c : C): Vec[S.unit]
  inline def zero: Vec[S.zero]
  inline def mul[m <: S](c : C, v : Vec[m]): Vec[m]
  import S._
  inline def cat[m <: S, n <: S](v1 : Vec[m], v2 : Vec[n]): Vec[m ⟐ n]
  //note: extension methods interact badly with trait inheritance, so it's better to have them delegate
  //to methods of the enclosing trait
  extension [m <: S](v : Vec[m])
    inline def ⊗(c : C): Vec[m] = mul(c, v)
  extension [m <: S, n <: S](v1 : Vec[m])   
    inline def ⊻(v2 : Vec[n]): Vec[m ⟐ n] = cat(v1,v2)
    //inline def ⊼(v2 : Vec[n]): Vec[m ⟐ n] 
   // TODO not sure about the other cat operator, the semantics suggests it's actually a split

/**
 * A quite literal translation of the paper, where we treat S-indexed vectors as functions from shapes to scalars.
 * These functions are total over a domain denoted by values s : S.
 */
/*trait CoEffAlgebraFun[C,S](using override val C : CoEffScalar[C], override val S : CoEffShapeSplit[S]) extends CoEffAlgebra[C,S] :
  type Ctx[s <: S]
  type Vec[s <: S] = Ctx[s] => C 
  inline def unit(c : C): Vec[S.unit] = _ => c
  inline def zero: Vec[S.zero] = _ => ???
  inline def mul[m <: S](c : C, v : Vec[m]) = (m : m) => c ⊗ v(m)
  import S._
  inline def cat[m <: S, n <: S](v1 : Vec[m], v2 : Vec[n]) = (mn : m ⟐ n) =>
    split(mn) match
      case m : m => v1(m)
      case n : n => v2(n)*/

/**
 * Analog to the function interpretation in terms of context funs.
 */
trait CoEffAlgebraCtxFun[C, S] (using override val C : CoEffScalar[C], override val S : CoEffShapeSplit[S]) extends CoEffAlgebra[C,S] :
  type Vec[s <: S] = s ?=> C
  inline def unit(c : C): Vec[S.unit] = _ ?=> c
  inline def zero: Vec[S.zero] = _ ?=> ???
  inline def mul[m <: S](c : C, v : Vec[m]) = (m : m) ?=> c ⊗ v
  import S._
  inline def cat[m <: S, n <: S](v1 : Vec[m], v2 : Vec[n]) = (mn : m ⟐ n) ?=>
    split(mn) match
      case m : m => v1(using m)
      case n : n => v2(using n)

object CoEffVector :
  import vec.Vectors._
  trait CoEffVectorAlg[C] extends CoEffAlgebra[C,Int] :
    private[this] def magic[A,B](a : A): B = a.asInstanceOf[B]
    override val S = StructShape
    type Vec[n <: Int] = Vector[n,C]
    inline def unit(c : C): Vec[S.unit] = magic(VCons(c, VNil))
    inline def zero: Vec[S.zero] = magic(VNil)
    inline def mul[m <: Int](c : C, v : Vec[m]): Vec[m] = v map (c ⊗ _)
    import S._
    inline def cat[m <: Int, n <: Int](v1 : Vec[m], v2 : Vec[n]): Vec[m ⟐ n] = magic(v1 ++ v2)

  given instance[C : CoEffScalar] : CoEffVectorAlg[C] with { override val C : CoEffScalar[C] = summon }
  def tests[C](using Alg : CoEffVectorAlg[C]) =
    import Alg._
    import Alg.C._

    val c1 = unit(use) ⊻ unit(ign)
    val c2 = zero ⊻ unit(ign) ⊻ unit(use ⊕ use ⊕ use) ⊻ unit(Alg.C.mul(use,ign)) //FIXME: for some reason, ⊗ and mul not found for C
    val c3 = c1 ⊻ c2
    val c4 = c3 ⊗ (Alg.C.mul(use ⊕ use ⊕ use, use ⊕ use))
    println(c1)
    println(c2)
    println(c3)
    println(c4)

  @main def run =
    println("#### Bounded Reuse ####")
    tests(using instance(using BoundedReuseSc))
    println("#### Dataflow ####")
    tests(using instance(using DataflowSc))
    println("#### Liveness ####")
    tests(using instance(using LivenessSc))



/**
 * The function interpretation for vectors above shows that a finer-grained distinction between
 * a particular shape s and the values that s denotes is sometimes desirable. A natural number
 * shape n can denote an n-product or a function with domain 0..n-1. The latter being a quite 
 * different type from shape n itself. We might need to slightly refactor the design of the 
 * type classes to make these distinctions clear. 
 */
object Fin :
  //type of sets with n values
  sealed trait Fin[n <: Int] 
  case class FZ[n <: Int]() extends Fin[n+1] {
    //inline val n = valueOf[n]
  }
  
  case class FS[n <: Int](pred : Fin[n]) extends Fin[n+1]
  
  val n : Fin[2] = FZ[1]()
  //val n : Fin[0] = FZ[0]()

  type Range[n <: Int, m <: Int] <: Int = m match
    case n => n
    case ? => m | Range[n, m-1]

  //Range[0,2] = 2 | 1 | 0

  type Finite[n <: Int] = Range[0,n]

  type cat[n <: Int, m <: Int] = Finite[n+m]

  type cat2[f1 <: [n <: Int] =>> Finite[n], f2 <: [n <: Int] =>> Finite[n]] = f1 match
    case ? => Any
