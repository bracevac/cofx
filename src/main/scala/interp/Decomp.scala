package interp

import scala.compiletime.{summonFrom, error, erasedValue, summonInline}
import scala.util.NotGiven
/**
 * A study on how to express coeffect scalar splitting at the type and term level.
 */
object Decomp :
  private[this] def magic[A,B](a : A): B = a.asInstanceOf[B]
  
  import peano.Nat._
  import peano.Arithmetic._
  import Common._
  
  sealed trait Vec[n <: Nat, +T] :
    def take[i<:Nat,j<:Nat](using NAdd[i,j,n]): Vec[i,T]
    def drop[i<:Nat,j<:Nat](using NAdd[i,j,n]): Vec[j,T]
    def dup[i<:Nat,j<:Nat](using mul : NMul[i,j,n]): Vec[i, Vec[j,T]] = mul match
      case NMulZLeft(j)        => VNil
      case NMulStep(prev,add)  => VCons(take(using add),drop(using add).dup(using prev))
    def map[U >: T, V](f: U => V): Vec[n,V]
    def zip[U](that: Vec[n,U]): Vec[n,(T,U)]
    def extract(using NotGiven[n =:= Z.type]): T //TODO: paper demands neutral element (e.g. 1) here, is this important?
    def toList: List[T]
    override def toString: String = s"⟨${this.toList.map(_.toString).mkString(",")}⟩"

  case object VNil extends Vec[Z.type, Nothing] :
    def take[i<:Nat,j<:Nat](using add : NAdd[i,j,Z.type]): Vec[i,Nothing] = add match
      case NAddZ(_) => VNil     
    def drop[i<:Nat,j<:Nat](using add : NAdd[i,j,Z.type]): Vec[j,Nothing] = add match
      case NAddZ(_) => VNil
    def map[U >: Nothing, V](f: U => V) = VNil
    def zip[U](that: Vec[Z.type,U]): Vec[Z.type,(Nothing,U)] = VNil 
    def extract(using NotGiven[Z.type =:= Z.type]): Nothing = ???
    def toList = List()   
  
  case class VCons[n<:Nat,+T](hd : T, tl: Vec[n,T]) extends Vec[Suc[n], T] :
    def take[i<:Nat,j<:Nat](using add : NAdd[i,j,Suc[n]]): Vec[i,T] = add match 
      case NAddZ(_) => VNil
      case NAddStep(prev) => VCons(hd, tl.take(using prev))
    def drop[i<:Nat,j<:Nat](using add : NAdd[i,j,Suc[n]]): Vec[j,T] = add match
      case NAddZ(_) => this
      case NAddStep(prev) => tl.drop(using prev)
    def map[U >: T, V](f: U => V) = VCons(f(hd), tl.map(f))
    def zip[U](that: Vec[Suc[n],U]): Vec[Suc[n],(T,U)] = that match
      case VCons(hd2, tl2) => VCons((hd,hd2), tl.zip(tl2))
    def extract(using NotGiven[Suc[n] =:= Z.type]): T = hd
    def toList = hd :: tl.toList
    
  //FIXME: what you really want here is ProductOf[y,x] instead of the relational NMul[y,x,yx] 
  def compose[x<:Nat,y<:Nat,yx<:Nat,A,B,C](f : Vec[x,A] => B, g : Vec[y,B] => C)(using NMul[y,x,yx]): Vec[yx,A] => C =
    v => g(v.dup[y,x].map(f))  
  
  /*
   * R = (r * s1,...,r * sn)
   */
  sealed trait ScalarMul[r<:Nat,S<:Tuple,R<:Tuple] 
  /*
   * -----------[SMBase]
   * <> = r ** <>
   */
  case class SMBase[r<:Nat](mul : NMul[r,Z.type,Z.type]) extends ScalarMul[r,EmptyTuple,EmptyTuple]
  given smbase[r<:Nat](using r : NMul[r,Z.type,Z.type]) : ScalarMul[r,EmptyTuple,EmptyTuple] = SMBase(r)
  /*
   * T = r ** S    rv = r * v
   * -----------------------[SMStep]
   * rv :* T = r ** (v *: S) 
   */
  case class SMStep[r<:Nat,v<:Nat,rv<:Nat,S<:Tuple,T<:Tuple](prev: ScalarMul[r,S,T], hdmul: NMul[r,v,rv]) extends ScalarMul[r,v *: S, rv *: T]    
  given smstep[r<:Nat,v<:Nat,rv<:Nat,S<:Tuple,T<:Tuple](using hdmul : NMul[r,v,rv])(using prev : ScalarMul[r,S,T]) : ScalarMul[r,v *: S, rv *: T] = SMStep(prev,hdmul)
   
  trait ScalarMulFun1[r<:Nat,T<:Tuple] :
     type S <: Tuple
  given [r<:Nat,U<:Tuple,T<:Tuple](using sm : ScalarMul[r,U,T]): ScalarMulFun1[r,T] with  
    type S = U
  
  //checks the invariant for Ctx that 1) R and A are same length, and 2) R has only Nat components
  sealed trait OK[R <: Tuple, A <: Tuple]
  /*
   * --------[OKEmpty]
   * <> <> OK
   */
  case object OKEmpty extends OK[EmptyTuple, EmptyTuple]
  given OK[EmptyTuple,EmptyTuple] = OKEmpty
  /*
   * R T OK  n \in Nat
   * --------------------[OKTCons]
   * (n *: R) (A *: T) OK
   */
  case class OKTCons[n<:Nat,R<:Tuple,A,T<:Tuple](rest_ok : OK[R,T]) extends OK[n *: R, A *: T]
  given [n<:Nat,R<:Tuple,A,T<:Tuple](using rest_ok : OK[R,T]) : OK[n *: R, A *: T] = OKTCons(rest_ok)

  sealed trait CatR[L<:Tuple,R<:Tuple,LR<:Tuple]
  case class CatZ[R<:Tuple]() extends CatR[Tup0,R,R]
  given catz[R<:Tuple] : CatR[EmptyTuple,R,R] = CatZ()
  case class CatSuc[X,L<:Tuple,R<:Tuple,LR<:Tuple](prev: CatR[L,R,LR]) extends CatR[X *: L, R, X *: LR]
  given cats[X,L<:Tuple,R<:Tuple,LR<:Tuple](using prev : CatR[L,R,LR]) : CatR[X *: L, R, X *: LR] = CatSuc(prev)
  
  //functional dependencies
  sealed trait Cat[L<:Tuple,R<:Tuple] : 
    type Res <: Tuple 
  given [L<:Tuple,R<:Tuple,LR<:Tuple](using CatR[L,R,LR]): Cat[L,R] with 
    type Res = LR 
  
  sealed trait SplitL[R<:Tuple,LR<:Tuple] : 
    type L <: Tuple
  given [L0<:Tuple,R<:Tuple,LR<:Tuple](using CatR[L0,R,LR]): SplitL[R,LR] with
    type L = L0 
  
  sealed trait SplitR[L<:Tuple,LR<:Tuple] : 
    type R <: Tuple
  given [L<:Tuple,R0<:Tuple,LR<:Tuple](using CatR[L,R0,LR]): SplitR[L,LR] with
    type R = R0

  sealed trait Cat2R[A<:Tuple,B<:Tuple,L<:Tuple,R<:Tuple,AB<:Tuple,LR<:Tuple]
  case class Cat2Z[R<:Tuple,A<:Tuple]() extends Cat2R[Tup0,R,Tup0,A,R,A]
  given cat2z[R<:Tuple,A<:Tuple] : Cat2R[Tup0,R,Tup0,A,R,A] = Cat2Z()
  case class Cat2Suc[R1<:Tuple,R2<:Tuple,R12<:Tuple,A1<:Tuple,A2<:Tuple,A12<:Tuple,S,X](prev: Cat2R[R1,R2,A1,A2,R12,A12]) extends Cat2R[S *: R1, R2, X *: A1, A2, S *: R12, X *: A12]
  given cat2s[R1<:Tuple,R2<:Tuple,R12<:Tuple,A1<:Tuple,A2<:Tuple,A12<:Tuple,S,X](using prev : Cat2R[R1,R2,A1,A2,R12,A12]) : Cat2R[S *: R1, R2, X *: A1, A2, S *: R12, X *: A12] = Cat2Suc(prev)
  //TODO functional dependencies

  sealed trait EqLen[A<:Tuple,B<:Tuple] :
    type Length <: Nat 
    val length : Length 
  given eqlenz : EqLen[EmptyTuple,EmptyTuple] with 
    type Length = Z.type 
    val length = Z 
  given eqlensuc[A<:Tuple,B<:Tuple,C,D](using prev: EqLen[A,B]) : EqLen[C *: A, D *: B] with 
    type Length = Suc[prev.Length]
    val length = Suc(prev.length)
  
  type Tup0 = EmptyTuple
  type Tup1[A] = A *: EmptyTuple
  //TODO: should the tuples be marked covariant? that requires some changes in signatures
  //TODO: context functions and type aliases might make this less painful
  //TODO: restore OK guard (makes trouble in dup method for CCons)
  sealed trait Ctx[R <: Tuple, A <: Tuple] : //(using OK[R,A]) :
    //for singleton context, we have an indexed comonad with ops TODO: make an n-ary fmap 
    def map[B,n<:Nat,C](f: B => C)(using A =:= Tup1[B], R =:= Tup1[n]): Ctx[R, Tup1[C]]
    def mapV[B,n<:Nat,C](f: Vec[n,B] => Vec[n,C])(using A =:= Tup1[B], R =:= Tup1[n]): Ctx[R, Tup1[C]]
    def extract[B,n<:Nat](using A =:= Tup1[B], R =:= Tup1[n])(using NotGiven[n =:= Z.type]): B //TODO: this could also be generalized to n-ary
    def dup[B,i<:Nat,j<:Nat,n<:Nat](using A =:= Tup1[B], R =:= Tup1[n])(using NMul[i,j,n]): Ctx[Tup1[i], Tup1[Ctx[Tup1[j], Tup1[B]]]]
    //structural indexed comonad ops TODO: I think this makes the other dup redundant
    def dup[r<:Nat,S<:Tuple](using sm : ScalarMul[r,S,R]): Ctx[Tup1[r], Tup1[Ctx[S,A]]] 
    def dup[r<:Nat,S<:Tuple](r : r)(using sm : ScalarMul[r,S,R]): Ctx[Tup1[r], Tup1[Ctx[S,A]]] = dup(using sm) 
    //context splitting/merging
    def m[R2<:Tuple,A2<:Tuple,R3<:Tuple,A3<:Tuple](that : Ctx[R2, A2])(using Cat2R[R,R2,A,A2,R3,A3]): Ctx[R3, A3]
    def n[R1<:Tuple,R2<:Tuple,A1<:Tuple,A2<:Tuple](using Cat2R[R1,R2,A1,A2,R,A]): (Ctx[R1,A1], Ctx[R2,A2])
    def toList : List[Any]
    override def toString() = 
      val strs = toList.map(_.toString).mkString(" • ") 
      s"⦉${if strs.isEmpty then "" else s" $strs " }⦊"   

  case object CNil extends Ctx[Tup0,Tup0] : //(using OKEmpty) :
    def map[B,n<:Nat,C](f: B => C)(using Tup0 =:= Tup1[B], Tup0 =:= Tup1[n]): Ctx[Tup0, Tup1[C]] = ???
    def mapV[B,n<:Nat,C](f: Vec[n,B] => Vec[n,C])(using Tup0 =:= Tup1[B], Tup0 =:= Tup1[n]): Ctx[Tup0, Tup1[C]] = ???
    def extract[B,n<:Nat](using Tup0 =:= Tup1[B], Tup0 =:= Tup1[n])(using NotGiven[n =:= Z.type]): B = ???
    def dup[B,i<:Nat,j<:Nat,n<:Nat](using Tup0 =:= Tup1[B], Tup0 =:= Tup1[n])(using NMul[i,j,n]): Ctx[Tup1[i], Tup1[Ctx[Tup1[j], Tup1[B]]]] = ???     
    def dup[r<:Nat,S<:Tuple](using sm : ScalarMul[r,S,Tup0]): Ctx[Tup1[r], Tup1[Ctx[S,Tup0]]] = sm match
      case SMBase(mulr0) => CCons(VNil.dup(using mulr0).map(_ => CNil), CNil)
    def m[R2<:Tuple,A2<:Tuple,R3<:Tuple,A3<:Tuple](that : Ctx[R2, A2])(using cat : Cat2R[Tup0,R2,Tup0,A2,R3,A3]): Ctx[R3, A3] = cat match 
      case Cat2Z() => that
    def n[R1<:Tuple,R2<:Tuple,A1<:Tuple,A2<:Tuple](using cat : Cat2R[R1,R2,A1,A2,Tup0,Tup0]): (Ctx[R1,A1], Ctx[R2,A2]) = cat match
      case Cat2Z() => (CNil, CNil)
    def toList = Nil
        
  case class CCons[n<:Nat,R<:Tuple,A,T <:Tuple](hd : Vec[n,A], tl : Ctx[R,T])/*(using OK[R,T])*/ extends Ctx[n *: R, A *: T] :
    //FIXME it seems the compiler is too stupid to figure out congruences like (n *: R) =:= Tup1[m] implies n =:= m, can we do these manually?
    def map[B,m<:Nat,C](f: B => C)(using eq1 : (A *: T) =:= Tup1[B], eq2 : (n *: R) =:= Tup1[m]): Ctx[n *: R, Tup1[C]] =
      mapV[B,m,C](_.map(f))
    def mapV[B,m<:Nat,C](f: Vec[m,B] => Vec[m,C])(using (A *: T) =:= Tup1[B], (n *: R) =:= Tup1[m]): Ctx[n *: R, Tup1[C]] =
      CCons(magic(f(magic(hd))), magic(CNil))  
    def extract[B,m<:Nat](using (A *: T) =:= Tup1[B], (n *: R) =:= Tup1[m])(using NotGiven[m =:= Z.type]): B = 
      magic(hd.extract)
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
    def toList = hd :: tl.toList   
     
  //arrow composition 
  type Ctx1[r<:Nat,X] = Ctx[Tup1[r],Tup1[X]]
  def compose[S<:Tuple,A<:Tuple,B,r<:Nat,C,rS<:Tuple](f : Ctx[S,A] => B, g : Ctx1[r,B] => C)(using sm: ScalarMul[r,S,rS]): Ctx[rS,A] => C =
    crS => g(crS.dup(using sm).map(f)) 
  
  @main def decomp_tests() =
    val v1 = VCons(1,VCons(2, VCons(3, VCons(4, VCons(5, VCons(6, VNil)))))) //6
    val v2 = VCons(4, VCons(3, VCons(2, VCons(1, VNil)))) //4
    val v3 = VCons("A", VCons("B", VNil)) //2
    val c : Ctx[(_6,_4,_2),(Int,Int,String)] = CCons(v1, CCons(v2, CCons(v3, CNil))) //D[3,(6,4,2)](Int x Int x String)
    val tests = List(
      nat[10], 
      summon[Suc[Suc[Z.type]]],
      summon[NAdd[_0,_1,_1]],
      summon[NAdd[_2,_4,_6]],
      summon[NAdd[_4,_2,_6]],
      summon[NMul[_1,_4,_4]],
      summon[NMul[_4,_1,_4]],
      summon[NMul[_2,_2,_4]],
      summon[NMul[_2,_0,_0]],
      v1.dup[_1,_6],
      v1.dup[_6,_1],
      v1.dup[_2,_3],
      v1.dup[_3,_2],
      VNil.dup[_0,_6],
      VNil.dup[_6,_0],
      v1.dup[_6,_1] zip VNil.dup[_6,_0],
      v1 zip v1,
      v1.dup[_2,_3] zip v1.dup[_2,_3],
      CNil.dup[_5,EmptyTuple],
      "Dup",
      c,//D[3,(6,4,2)](Int x Int x String) 
      c.dup[nat[2], (_3,_2,_1)], //FIXME: annoying that the (_3,_2,_1) has to be specified too
      c.dup[nat[1], (_6,_4,_2)].dup[nat[1],nat[1] *: EmptyTuple].dup[nat[1],nat[1] *: EmptyTuple].dup[nat[1],nat[1] *: EmptyTuple],
      c.m(c),
      c.n[(_6,_4,_2),Tup0,(Int,Int,String),Tup0],
      c.n[(_6,_4),Tup1[_2],(Int,Int),Tup1[String]], //TODO: should we have a version where only half of the type parameters are needed?
      c.n[Tup1[_6],(_4,_2),Tup1[Int],(Int,String)],
      c.n[Tup0,(_6,_4,_2),Tup0,(Int,Int,String)],
      c.n[Tup1[_6],(_4,_2),Tup1[Int],(Int,String)]._2.m(c.n[Tup1[_6],(_4,_2),Tup1[Int],(Int,String)]._1)
    )
    summon[NMul[_2,_0,_0]]
    summon[ScalarMulFun1[_2, EmptyTuple]]
    summon[SummandR[_2,_2]]
    summon[SummandR[_1,_2]]
    summon[SummandL[_2,_2]]
    summon[SummandL[_1,_2]]
    summon[SummandR[_0,_0]]
    summon[SumOf[_5,_5]]
    summon[CatR[(_3,_2,_1),(_6,_4,_2),(_3,_2,_1,_6,_4,_2)]]
    summon[Cat[(_3,_2,_1),(_6,_4,_2)]]
    val splitl = summon[SplitL[(_6,_4,_2),(_3,_2,_1,_6,_4,_2)]]
    summon[SplitR[(_3,_2,_1),(_3,_2,_1,_6,_4,_2)]]
    summon[splitl.L =:= (_3,_2,_1)] 
    //FIXME: ProductOf and FactorR/L resolution never works
    //summon[ProductOf[_3,_1]]   
    //summon[ProductOf[nat[5],nat[9]]]
    //summon[ScalarMulFun1[_2, _2 *: EmptyTuple]] 
    val f = summon[SummandR[nat[3],nat[9]]] 
    val g : f.r = nat[6] 
    val t = summon[SummandL[nat[3],nat[9]]]
    val u : t.l = g
    /*val h = summon[SumOf[nat[10],nat[13]]]
    summon[nat[23] =:= h.sum]
    val minus = summon[SummandL[nat[20],h.sum]]
    summon[minus.l =:= nat[3]]*/ 
    tests.foreach(println(_))

end Decomp 