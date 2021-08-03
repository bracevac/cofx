package interp

import scala.compiletime.{summonFrom, error, erasedValue, summonInline}
import scala.util.NotGiven
import scala.compiletime.ops.int._
/**
 * A study on how to express coeffect scalar splitting at the type and term level.
 */
object DecompNew :


  trait CoeffScalar[C]:

    type use <: C
    type ign <: C

    trait Add[A<:C,B<:C,R<:C]
    trait Mul[A<:C,B<:C,R<:C]


  trait IndexedComonad[S, D[_ <:S, _], C <: CoeffScalar[S]](using val s: C):

    def dup[i <: S, j <: S, n <: S, T](d: D[n, T])(using s.Mul[i, j, n]): D[i, D[j, T]]
    def extract[n <: S, T](d : D[n,T])(using NotGiven[n =:= s.use]): T
    def map[n <: S, A, B](d : D[n,A], f : A => B) : D[n,B]
  
  
  import Tuple._
  type Tup0 = EmptyTuple
  type Tup1[A] = A *: Tup0
  
  trait ScalarMul[S](using val s: CoeffScalar[S]):
    sealed trait ScalarMul[r<:S,I<:Tuple,O<:Tuple]
    case class SMBase[r<:S](mul : s.Mul[r,s.use,s.use]) extends ScalarMul[r,Tup0,Tup0]
    given smbase[r<:S](using r : s.Mul[r,s.use,s.use]) : ScalarMul[r,Tup0,Tup0] = SMBase(r)
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
  
  trait Context[S, D[_<:S,_]](using val sm: ScalarMul[S]):

    trait Ctx[R <: Tuple, V <: Tuple]:
      def fmap[F <: Tuple, O <: Tuple](f: F)(using ev: MapEv[F, R, O]): Ctx[O, V]
      //Definitely unsafe
      def extract[n <: Int](using notZero: n > 0): Elem[V, n]
      def dup[r <: S, I <: Tuple](using smEv: sm.ScalarMul[r,I,R]): Ctx[Tup1[r], Tup1[Ctx[I,V]]] 
      def m[R2<:Tuple,V2<:Tuple,R3<:Tuple,V3<:Tuple](that : Ctx[R2,V2])(using cat: Cat2R[R,R2,V,V2,R3,V3]): Ctx[R3,V3]
      def n[R1<:Tuple,R2<:Tuple,V1<:Tuple,V2<:Tuple](using cat: Cat2R[R1,R2,V1,V2,R,V]): (Ctx[R1,V1], Ctx[R2,V2])
  
    case object CNil extends Ctx[Tup0,Tup0]:
      def fmap[F <: Tuple, O <: Tuple](f: F)(using ev: MapEv[F, Tup0, O]): Ctx[O, Tup0] = ???
      def extract[n <: Int](using notZero: n > 0): Elem[Tup0, n] = ???
      def dup[r <: S, I <: Tuple](using smEv: sm.ScalarMul[r,I,Tup0]): Ctx[Tup1[r], Tup1[Ctx[I,Tup0]]] = sm match
        case sm.SMBase(mulr0) => ???//CCons(VNil.dup(using mulr0).map(_ => CNil), CNil)
      def m[R2<:Tuple,V2<:Tuple,R3<:Tuple,V3<:Tuple](that : Ctx[R2,V2])(using cat: Cat2R[Tup0,R2,Tup0,V2,R3,V3]): Ctx[R3,V3] = cat match 
        case Cat2Z() => that
      def n[R1<:Tuple,R2<:Tuple,V1<:Tuple,V2<:Tuple](using cat: Cat2R[R1,R2,V1,V2,Tup0,Tup0]): (Ctx[R1,V1], Ctx[R2,V2]) = cat match
        case Cat2Z() => (CNil, CNil)
      def toList = Nil
    
    /*
    case class CCons[n<:Int,R<:Tuple,A,V <:Tuple](hd : D[n,A], tl : Ctx[R,V])/*(using OK[R,T])*/ extends Ctx[n *: R, A *: V] :
      //FIXME it seems the compiler is too stupid to figure out congruences like (n *: R) =:= Tup1[m] implies n =:= m, can we do these manually?
      def fmap[F <: Tuple, O <: Tuple](f: F)(using ev: MapEv[F, R, O]): Ctx[O, V] = ???
        //mapV[B,m,C](_.map(f))
      //def mapV[B,m<:Nat,C](f: Vec[m,B] => Vec[m,C])(using (A *: T) =:= Tup1[B], (n *: R) =:= Tup1[m]): Ctx[n *: R, Tup1[C]] =
      //  CCons(magic(f(magic(hd))), magic(CNil))  
      def extract[B,m<:Int](using (A *: V) =:= Tup1[B], (n *: R) =:= Tup1[m])(using NotGiven[m =:= Z.type]): Elem[V,n] = ???
        //magic(hd.extract)
      def dup[B,i<:Nat,j<:Nat,m<:Nat](using (A *: T) =:= Tup1[B], (n *: R) =:= Tup1[m])(using mul : NMul[i,j,m]): Ctx[Tup1[i], Tup1[Ctx[Tup1[j], Tup1[B]]]] =
        CCons(hd.dup[i,j](using magic(mul)).map(c => CCons(magic(c),CNil)),CNil)
      def dup[r<:Nat,S<:Tuple](using sm : ScalarMul[r,S,n *: R]): Ctx[Tup1[r], Tup1[Ctx[S,A *: T]]] = sm match
        case SMStep(prev, hdmul) => 
          val CCons(ctl,CNil) = tl.dup(using prev)  //Ctx[<r>, Ctx[S',T]] for some S' w. r ** S' = R
          val hdd = hd.dup(using hdmul)             //Vec[r, Vec[v,A]
          CCons((hdd zip ctl) map {case (h,c) => CCons(h,c)},CNil)
      def m[R2<:Tuple,A2<:Tuple,R3<:Tuple,A3<:Tuple](that : Ctx[R2, A2])(using cat : Cat2R[n *: R,R2,A *: T,A2,R3,A3]): Ctx[R3, A3] = cat match
        case Cat2Suc(prev) => CCons(hd, tl.m(that)(using prev))
      def n[R1<:Tuple,R2<:Tuple,A1<:Tuple,A2<:Tuple](using cat : Cat2R[R1,R2,A1,A2,n *: R,A *: T]): (Ctx[R1,A1], Ctx[R2,A2]) = cat match
        case Cat2Z()        => (CNil, this)
        case Cat2Suc(prev) => 
          val (c1, c2) = tl.n(using prev)
          (CCons(hd,c1), c2)
      def toList = hd :: tl.toList*/

end DecompNew

object Test extends App:
  type _0 = 0
  val  _0 = 0
  type _1 = 1
  val  _1 = 1
  type _2 = 2
  val  _2 = 2



  