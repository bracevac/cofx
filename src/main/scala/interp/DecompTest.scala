package interp

import scala.compiletime.{summonFrom, error, erasedValue, summonInline}
import scala.util.NotGiven
import scala.compiletime.ops.int._
/**
 * A study on how to express coeffect scalar splitting at the type and term level.
 */
object DecompNew :


  trait CoeffScalar[C]:

    type zero <: C
    type one <: C

    trait Add[A<:C,B<:C,R<:C]
    trait Mul[A<:C,B<:C,R<:C]
  
  /**  
  trait CoeffScalar[S]:

    type zero <: S
    type one <: S
 
    trait Scalar[S]
    case object ign extends Scalar[zero]
    case object use extends Scalar[one]
    case class Suc(s: S) extends Scalar[S]

    trait Add[A<:S,B<:S,C<:S]
    trait Mul[A<:S,B<:S,C<:S]

    //case class CSAddZ[r<:S]() extends Add[zero, r, r]
    //case class CSAddStep[l <: S, r <: S, res <:S](prev : Add[l,r,res]) extends Add[Suc[l], r, Suc[res]]
  **/


  trait IndexedComonad[S, D[_ <:S, _], C <: CoeffScalar[S]](using val s: C):

    def dup[i <: S, j <: S, n <: S, T](d: D[n, T])(using s.Mul[i, j, n]): D[i, D[j, T]]
    def extract[n <: S, T](d : D[n,T])(using NotGiven[n =:= s.zero]): T
    def map[n <: S, A, B](d : D[n,A], f : A => B) : D[n,B]
  
  
  import Tuple._
  type Tup0 = EmptyTuple
  type Tup1[A] = A *: Tup0
  
  trait ScalarMul[S](using val s: CoeffScalar[S]):
    sealed trait ScalarMul[r<:S,I<:Tuple,O<:Tuple]
    case class SMBase[r<:S](mul : s.Mul[r,s.zero,s.zero]) extends ScalarMul[r,Tup0,Tup0]
    given smbase[r<:S](using r : s.Mul[r,s.zero,s.zero]) : ScalarMul[r,Tup0,Tup0] = SMBase(r)
    case class SMStep[r<:S,v<:S,rv<:S,I<:Tuple,O<:Tuple](prev: ScalarMul[r,I,O], hdmul: s.Mul[r,v,rv]) extends ScalarMul[r,v *: I, rv *: O]    
    given smstep[r<:S,v<:S,rv<:S,I<:Tuple,O<:Tuple](using hdmul : s.Mul[r,v,rv])(using prev : ScalarMul[r,I,O]) : ScalarMul[r,v *: I, rv *: O] = SMStep(prev,hdmul)
  

  sealed trait MapEv[F <: Tuple, I <: Tuple, O <: Tuple]
  case object EmptyEv extends MapEv[Tup0, Tup0, Tup0]
  case class ConsEv[A, B, F <: A => B, R <: Tuple, S <: Tuple, T <: Tuple](prev:  MapEv[R, S, T]) extends MapEv[F *: R, A *: S, B *: T]
  given consev[A, B, F <: A => B, R <: Tuple, S <: Tuple, T <: Tuple](using prev:  MapEv[R, S, T]): MapEv[F *: R, A *: S, B *: T]  = ConsEv(prev)

  sealed trait Cat2R[A<:Tuple,B<:Tuple,L<:Tuple,R<:Tuple,AB<:Tuple,LR<:Tuple]
  case class Cat2Z[R<:Tuple,A<:Tuple]() extends Cat2R[Tup0,R,Tup0,A,R,A]
  given cat2z[R<:Tuple,A<:Tuple] : Cat2R[Tup0,R,Tup0,A,R,A] = Cat2Z()
  case class Cat2Suc[R1<:Tuple,R2<:Tuple,R12<:Tuple,A1<:Tuple,A2<:Tuple,A12<:Tuple,S,X](prev: Cat2R[R1,R2,A1,A2,R12,A12]) extends Cat2R[S *: R1, R2, X *: A1, A2, S *: R12, X *: A12]
  given cat2s[R1<:Tuple,R2<:Tuple,R12<:Tuple,A1<:Tuple,A2<:Tuple,A12<:Tuple,S,X](using prev : Cat2R[R1,R2,A1,A2,R12,A12]) : Cat2R[S *: R1, R2, X *: A1, A2, S *: R12, X *: A12] = Cat2Suc(prev)
  
  trait Ctx[S, R <: Tuple, V <: Tuple](using val sm: ScalarMul[S]):
    def fmap[F <: Tuple, O <: Tuple](f: F)(using ev: MapEv[F, R, O]): Ctx[S, O, V]
    //Definitely unsafe
    def extract[n <: Int](using notZero: n > 0): Elem[V, n]
    def dup[r <: S, I <: Tuple](using smEv: sm.ScalarMul[r,I,R]): Ctx[S, Tup1[r], Tup1[Ctx[S,I,V]]] 
    def m[R2<:Tuple,V2<:Tuple,R3<:Tuple,V3<:Tuple](that : Ctx[S,R2,V2])(using Cat2R[R,R2,V,V2,R3,V3]): Ctx[S,R3,V3]
    def n[R1<:Tuple,R2<:Tuple,V1<:Tuple,V2<:Tuple](using Cat2R[R1,R2,V1,V2,R,V]): (Ctx[S,R1,V1], Ctx[S,R2,V2])


end DecompNew

object Test extends App:
  type _0 = 0
  val  _0 = 0
  type _1 = 1
  val  _1 = 1
  type _2 = 2
  val  _2 = 2



  