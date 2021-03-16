package interp

import scala.compiletime.ops.int._
import scala.compiletime.{S, summonFrom, error, erasedValue}
import Common._

/**
 * Coeffscalars are supposed to induce a (strict) monoidal category, essentially lifting the
 * monoid ops of the scalar into the type level. 
 * @tparam C
 */
trait Monoidal[C] :
  type ⊗[c1 <: C, c2 <: C] <: C //TODO should be a bifunctor
  type I <: C 
  def bimap[A <: C,B <: C,X <: C,Y <:C ]: (A ⊗ B) => (A => X) => (B => Y) => (X ⊗ Y) 

/**
 * Indexed comonads.
 */
trait IndexedComonad[C, F <: [c <: C] =>> [X] =>> Any](using val M : Monoidal[C]) :
  import M._
  def dup[x <: C, y <: C]: F[x ⊗ y] ~> (F[x] ⨀ F[y]) //F[x][F[y][A]]
  def extract : F[I] ~> Id 
  def fmap[c<:C, A,B]: F[c][A] => (A => B) => F[c][B]
  def compose[x <: C, y <: C, A, B, X](g : F[y][B] => X, f : F[x][A] => B): F[y ⊗ x][A] => X = 
  { x => g(fmap[y,F[x][A],B](dup[y,x][A](x))(f)) }

/**
 * Structural indexed comonads.
 * @tparam S type of coeffect shapes
 * @tparam C type of coeffect scalars
 */
trait StructComonad[S, C](using shape0: CoEffShape[S], scalar0 : CoEffScalar[C])(using mon: Monoidal[C], alg: CoEffAlgebra[C,S]) :
  given shape    : CoEffShape[S]     = shape0 
  given scalar   : CoEffScalar[C]    = scalar0
  given algebra  : CoEffAlgebra[C,S] = alg
  given monoidal : Monoidal[C]       = mon
  //TODO might need to demand a stronger connection between scalar and monoidal 
  
  final type Vec1 = algebra.Vec[shape.unit]
  final type STuple1 = STuple[shape.unit]
  
  type STuple[s <: S] <: Tuple
  type D[s <: S] <: [v <: algebra.Vec[s]] =>> [X <: STuple[s]] =>> Any //TODO should satisfy functor
  
  final type D1 = [v <: Vec1] =>> [X] =>> Any 
  //D[S.unit] is supposed to be an indexed comonad  
  given unitComonad : IndexedComonad[Vec1, D1]
  /*
   * FIXME: upper-bounding D's third parameter with STuple[s] makes D1 incompatible with the bounds demanded in the
   * IndexedComonad interface. But somehow, we need to say that we have a variable number of type arguments
   * as determined by the shape parameter s. We need an alternate encoding of the dependent product for D.
   */




  

    
    

  