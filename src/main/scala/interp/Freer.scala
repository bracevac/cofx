package interp



import scala.annotation.implicitNotFound
import scala.language.{higherKinds, implicitConversions}
import scala.util.NotGiven

//Track effects as type-level lists of type constructors
object Eff :
  sealed trait Eff
  trait ∅ extends Eff
  trait ⊗[A[_], TL <: Eff] extends Eff
  type Lone[T[_]] = T ⊗ ∅
  
  sealed trait IsNothing[-T]
  object IsNothing :
    given inferredNothing : IsNothing[Nothing] with { }
  
//union type as in the freer monad paper, scala-style
object OpenUnion :
  import Eff.{given, _}

  sealed trait U[R <: Eff, X] :
    def weaken[E[_]]: U[E ⊗ R, X]
  case class Union[R<:Eff,T[_],X] private[OpenUnion](index: Int, value: T[X]) extends U[R,X] :
    def weaken[E[_]] = Union(index+1, value)
  object U :
    extension [R <: Eff, R2 <: Eff, K, X <: Eff](u : U[R,K]) 
      def weakenL(using cat : RowConcat[X,R,R2]): U[R2,K] = u match {
        case Union(n, v) => Union(n + cat.n, v) 
      }
  
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
        def prj[X](u: U[R,X]): Option[T[X]] = u match {
          case Union(i, v) if i == ptr.pos => Some(v.asInstanceOf[T[X]])
          case _ => None
        }

  @implicitNotFound("Cannot concatenate RowConcat[${A}, ${B}, ${C}]")
  trait RowConcat[A <: Eff, B <: Eff, C <: Eff](val n : Int)
  object RowConcat :
    given concat1[R <: Eff] : RowConcat[∅, R, R](0) with { }
    given concat2[E[_], R1 <: Eff, R2 <: Eff, R3 <: Eff]
                 (using prev: RowConcat[R1, R2, R3]): RowConcat[E ⊗ R1, R2, E ⊗ R3](prev.n + 1) with { } 
  
  //TODO can this be made more flexible? i.e. have decomp at arbitrary positions in the list R?
  def decomp[T[_], R <: Eff, X](u: U[(T ⊗ R),X]): Either[U[R,X], T[X]] = u match {
    case Union(0, v) => Right(v.asInstanceOf[T[X]])
    case Union(n, v) => Left(Union(n-1, v))
  }

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
  
  given extract[A] : Conversion[Comp[∅, A], A] = {
    case Return(a) => a
    case _ => ??? //dead code, avoids compiler warning  
  }

object Handlers :
  import Eff._
  import OpenUnion._
  import Freer._

  trait H[F[_], R <: Eff, A, B] :
    def ret(r : Return[F ⊗ R, A]): Comp[R,B]
    def handle[X](fx : F[X], k: X => Comp[R,B]): Comp[R,B]
  
  given hpat[F[_], R <: Eff, A, B] : Conversion[ [X] => (Return[F ⊗ R, A] | (F[X], X => Comp[R,B])) => Comp[R,B], H[F,R,A,B]] with
    def apply(f : [X] => (Return[F ⊗ R, A] | (F[X], X => Comp[R,B])) => Comp[R,B]): H[F,R,A,B] = new H {
      def ret(r : Return[F ⊗ R, A]) = f(r)
      def handle[Y](fx : F[Y], k: Y => Comp[R,B]) = f((fx, k))
    }

  def handler[E[_], R <: Eff, A, B](h: H[E, R, A, B]): Comp[E ⊗ R, A] => Comp[R, B] = {
    case Return(x) => h.ret(Return(x))
    case Op(u, k) => decomp(u) match {
      case Right(ex) =>
        h.handle(ex, x => handler(h)(k(x)))
      case Left(op) =>
        Op(op, x => handler(h)(k(x)))
    }
  }
  
  
object Demo :
  import Eff._
  import OpenUnion._
  import Freer._
  import Handlers.{_,given}

  sealed trait State[+S,K]
  case class Put[S](value : S) extends State[S,Unit]
    
  type IntST = [K] =>> State[Int,K]

 

  


  


