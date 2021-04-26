package interp2

import scala.annotation.implicitNotFound
import scala.language.{higherKinds, implicitConversions}
import scala.util.NotGiven
import scala.compiletime.summonFrom
import scala.compiletime.ops.int._
import scala.compiletime.{constValue}

//Track effects as type-level lists of type constructors
object Eff :
  sealed trait Eff
  trait ∅ extends Eff
  trait ⊗[A[_], TL <: Eff] extends Eff

  //type-level concatenation
  type @@[R <: Eff, T <: Eff] <: Eff = R match
    case ∅         => T
    case ⊗[hd, tl] => hd ⊗ (tl @@ T)
  
  //type-level length 
  type Len[R <: Eff] <: Int = R match
    case ∅         => 0
    case ⊗[hd, tl] => 1 + Len[tl]
  
  //term-level length
  sealed trait LenR[R <: Eff, N <: Int] :
    val value : Int
  given LenR[∅,0] with { val value = 0 }
  given lenRsucc[R <: Eff, N <: Int, T[_]](using pred : LenR[R,N]) : LenR[T ⊗ R, S[N]] with
    val value = 1 + pred.value 
  
  sealed trait IsNothing[-T]
  object IsNothing :
    given inferredNothing : IsNothing[Nothing] with { }
 
//union type as in the freer monad paper, scala-style
object OpenUnion :
  import Eff.{given, _}

  sealed trait U[R <: Eff, X] :
    def weaken[S <: Eff, N <: Int](using LenR[S,N]): U[S @@ R, X]
  case class Union[R<:Eff,T[_],X] private[OpenUnion](index: Int, value: T[X]) extends U[R,X] :
    def weaken[S <: Eff, N <: Int](using l : LenR[S,N]) = Union(index+l.value, value)
    
  //type-safe pointers into tlists
  trait PtrLvl1
  object PtrLvl1 :
    given ps[T[_], R <: Eff, U[_]](using pred: Ptr[T, R]): Ptr[T, U ⊗ R] = Ptr(pred.pos + 1)
  case class Ptr[T[_], R <: Eff] private[OpenUnion](pos: Int) extends PtrLvl1
  object Ptr :
    given pz[T[_], R <: Eff](using NotGiven[IsNothing[R]]): Ptr[T, T ⊗ R] = Ptr(0)
    
  @implicitNotFound("Cannot prove that ${T} is in the effect row ${R}")
  trait ∈[T[_], R <: Eff] : 
    def inj[X](sub: T[X]): U[R, X]
    def prj[X](u: U[R,X]): Option[T[X]]
  object ∈ :
    given member[T[_], R <: Eff](using ptr: Ptr[T, R]) : (T ∈ R) with     
        def inj[X](sub: T[X]): U[R,X] = Union(ptr.pos, sub)
        def prj[X](u: U[R,X]): Option[T[X]] = u match 
          case Union(i, v) if i == ptr.pos => Some(v.asInstanceOf[T[X]])
          case _ => None
  
  //TODO can this be made more flexible? i.e. have decomp at arbitrary positions in the list R?
  def decomp[T[_], R <: Eff, X](u: U[(T ⊗ R),X]): Either[U[R,X], T[X]] = u match 
    case Union(0, v) => Right(v.asInstanceOf[T[X]])
    case Union(n, v) => Left(Union(n-1, v))
  

  

object Freer :
  import Eff._
  import OpenUnion._

  sealed trait Comp[R <: Eff, +A] :
    def flatMap[B](f: A => Comp[R, B]): Comp[R, B]
    def map[B](f: A => B): Comp[R, B]
    def >>=[B](f: A => Comp[R, B]): Comp[R, B] = flatMap(f)

  case class Return[R <: Eff, A](a: A) extends Comp[R, A] :
    override def flatMap[B](f: A => Comp[R, B]): Comp[R, B] = f(a)
    override def map[B](f: A => B): Comp[R, B] = Return(f(a))

  //TODO use the construction from sec. 3.1 for the continuations
  case class Op[R <: Eff, A, X](op: U[R,X], k: X => Comp[R, A]) extends Comp[R, A] :
    override def flatMap[B](f: A => Comp[R, B]): Comp[R, B] =
      Op(op, x => k(x) >>= f )

    override def map[B](f: A => B): Comp[R, B] =
      Op(op, x => k(x) map f )

  def perform[T[_], R <: Eff, X](op: T[X])(using I: T ∈ R): Comp[R, X] = //TODO naming
    Op(I.inj(op), Return(_))

  def ret[R <: Eff, A] = Return[R,A] 
  
  given extract[A] : Conversion[Comp[∅, A], A] = 
    case Return(a) => a
    case _ => ??? //dead code, avoids compiler warning
/*
object Handlers :
  import Eff._
  import OpenUnion._
  import Freer._
  
  trait HClause[F[_], X] :
    type Ret
    val op : F[Ret]
    val cont : Ret => X 
  object HClause :
    def apply[F[_], X, Y](f : F[X], k : X => Y): HClause[F,Y] = new HClause :
      type Ret = X
      val op = f 
      val cont = k
    def unapply[F[_], X](h : HClause[F,X]): (F[h.Ret], h.Ret => X) = (h.op, h.cont)
      
  type Hndl[F[_], R <: Eff, A, B] = (Return[F ⊗ R, A] | HClause[F, Comp[R,B]]) => Comp[R,B]

  def handler[E[_], R <: Eff, A, B](h: Hndl[E, R, A, B]): Comp[E ⊗ R, A] => Comp[R, B] = 
    case Return(x) => h(Return(x))
    case Op(u, k)  => decomp(u) match 
      case Right(ex) =>
        h(HClause(ex, x => handler(h)(k(x))))
      case Left(op)  =>
        Op(op, x => handler(h)(k(x)))

  type Hndl2[F[_], R <: Eff, A, B] = [X] => (Return[F ⊗ R, A] | (F[X], X => Comp[R,B])) => Comp[R,B]

  def handler2[E[_], R <: Eff, A, B](h: Hndl2[E, R, A, B]): Comp[E ⊗ R, A] => Comp[R, B] =
    case Return(x) => h(Return(x))
    case Op(u, k)  => decomp(u) match
      case Right(ex) => 
        h(ex, x => handler(h)(k(x)))
      case Left(op) =>
        Op(op, x => handler(h)(k(x)))

object Demo :
  import Eff._
  import OpenUnion._
  import Freer._
  import Handlers.{_,given}

  sealed trait StateEff[+S,K]
  type State[+S] = [K] =>> StateEff[S,K]
  case class Put[S](value : S) extends StateEff[S,Unit]
  object Put$ :
    def unapply[S,R<:Eff,X](h : HClause[State[S],Comp[R,X]]) : (S, Unit => Comp[R,X]) = h match
      case HClause(Put(v), k) => (v.asInstanceOf[S],k.asInstanceOf[Unit => Comp[R,X]])
  
  val test = handler[State[Int], ∅, Unit, Int] {
    case Return(()) => ret(1)
    case Put$(v : Int, k) => k(()) >>= { (x : Int) => ret(v + x)}
  }

*/

  
  


  


