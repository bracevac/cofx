package interp

import interp.Common._
import interp.Functor
import scala.Tuple._

type Tup0 = EmptyTuple
type Tup1[A] = A *: EmptyTuple

// Context in "open" style
object Contexts :
  private[this] def magic[A,B](a : A): B = a.asInstanceOf[B]
  
  
  trait Ctx[El[_]] :
    sealed trait CoEff[A <: Tuple] :
      def map[F[_]](f : El ~> F)(that : Ctx[F]): that.CoEff[A]
      /* As special case, provide the indexed comonad ops for singleton shapes */
      def extract[B](using A =:= Tuple1[B]): El[B]
      def fmap[B,C](f : B => C)(using A =:= Tuple1[B], Functor[El]): CoEff[Tuple1[C]]

    case object CNil extends CoEff[Tup0] :
      def map[F[_]](f : El ~> F)(that : Ctx[F]): that.CoEff[Tup0] = that.CNil
      def extract[B](using Tup0 =:= Tuple1[B]): El[B] = ???
      def fmap[B,C](f : B => C)(using Tup0 =:= Tuple1[B], Functor[El]): CoEff[Tuple1[C]] = ???
    
    case class CCons[A, T <: Tuple](hd: El[A], tl : CoEff[T]) extends CoEff[A *: T] :
      def map[F[_]](f : El ~> F)(that : Ctx[F]): that.CoEff[A *: T] = that.CCons(f(hd), tl.map(f)(that))
      def extract[B](using (A *: T) =:= Tuple1[B]): El[B] = magic(hd)
      def fmap[B,C](f : B => C)(using (A *: T) =:= Tuple1[B], Functor[El]): CoEff[Tuple1[C]] =
        CCons(hd.map(magic(f)), CNil) 
    
    def single[A](x : El[A]): CoEff[Tuple1[A]] = CCons(x, CNil)   
  
  def apply[E[_]] : Ctx[E] = new Ctx[E] {}

// Contexts in "closed style"
object CContexts :
  private[this] def magic[A,B](a : A): B = a.asInstanceOf[B]
  transparent trait C[E[_]] extends Ctx : 
     type El[X] = E[X]
  
  trait Ctx :
    type El[_]
    sealed trait CoEff[A <: Tuple]
    case object CNil extends CoEff[EmptyTuple]
    case class CCons[A, T <: Tuple](hd: El[A], tl : CoEff[T]) extends CoEff[A *: T]

    def map(that: Ctx)(f : El ~> that.El): C[that.El] = ???

  def apply[E[_]] : C[E] = new C[E] {}

/* Context in "open" style plus indexing with the envelope.
   This is better over the module style for certain transformations
   that change the envelope El[_] of the heterogeneous list to some El'[_], since
   it'd requires a pre-allocated module instance for El'.
   
   Problem here is that the indexed comonad and structural indexed comonads
   are not easily definable.
 */
object OContexts :
  private[this] def magic[A,B](a : A): B = a.asInstanceOf[B]
  type Tuple0 = EmptyTuple
  type Tuple1[A] = A *: EmptyTuple
  
  trait Monoidal[F[_]] :
    type Prod[X] <: F[X] 
    type Unit[X] <: F[X]
    def prod[A](x : F[A], y : F[A]): Prod[A]
    def unit[A]: Unit[A]
    extension [A](x : F[A])
      def ⊗(that: F[A]): Prod[A]
  
  //x : A ^(n1 + n2) 
  //n1' = [X] =>> n1, n2' = [X] =>> n2
  //n1' +' n2' = [X] =>> n1'[X] + n2'[X] 
  
  sealed trait Ctx[A <: Tuple, El[_]] : 
    def map[F[_]](f : El ~> F): Ctx[A,F]
    /* Following the coeffect paper, we require only the singleton contexts to be an indexed
       comonad. TODO: should these be rather factored out into a type class? */
    /* This should read fmap : (A => B) => Ctx[El,(A)] => Ctx[El,(B)]
       Note the difference to map! */
    def fmap[B,C](f: B => C)(using Functor[El], A =:= Tuple1[B]): Ctx[Tuple1[C],El]
    def extract[B](using A =:= Tuple1[B]): El[B]
    //def dup[B,F[_]](using eq : A =:= Tuple1[B], M : Monoidal[F])(using El[B] =:= M.Prod[B]): Ctx[A, M.Prod]    
   
  case class CNil[El[_]]() extends Ctx[Tuple0,El] :
    def map[F[_]](f : El ~> F): Ctx[Tuple0,F] = CNil()
    def fmap[B,C](f: B => C)(using Functor[El], Tuple0 =:= Tuple1[B]): Ctx[Tuple1[C],El] = ???
    def extract[B](using Tuple0 =:= Tuple1[B]): El[B] = ???
    //def dup[B](using eq : Tuple0 =:= Tuple1[B], M : Monoidal[El]): Ctx[Tuple0, M.Prod] = CNil()

  case class CCons[El[_], A, T <: Tuple](hd: El[A], tl : Ctx[T,El]) extends Ctx[A *: T, El] :
    def map[F[_]](f : El ~> F): Ctx[A *: T,F] = CCons(f(hd), tl.map(f))
    def fmap[B,C](f: B => C)(using F : Functor[El], eq : (A *: T) =:= Tuple1[B]): Ctx[Tuple1[C],El] =        
      CCons(F.map(magic(hd))(f), CNil())
    def extract[B](using (A *: T) =:= Tuple1[B]): El[B] = magic(hd)
    //def dup[B](using eq : (A *: T) =:= Tuple1[B], M : Monoidal[El]): Ctx[A *: T, M.Prod] = ???

/*
 * Synthesis of the previous ideas with the coeffects paper. In particular, we
 * index the context by two tuples A,R, with the invariant that they are always
 * the same length. A is again the "naked" context shape, and R is the annotated
 * coeffect scalar vector for each position. Additionally, the envelope is now
 * additionally indexed by the coeffect scalars. 
 * 
 * Intuitively, we have Ctx[(A1,...,An), (r1,...,rn), El] == (El[r1,A1], ... , El[rn,An])
 * 
 * E.g. El[n,A] = A^n for bounded reuse
 */
object OMContexts :
  private[this] def magic[A,B](a : A): B = a.asInstanceOf[B]
  type Tup0 = EmptyTuple
  type Tup1[A] = A *: EmptyTuple

  trait Monoidal[C] :
    type ⊗[c1, c2] 
    type I 
    def bimap[A,B,X,Y]: (A ⊗ B) => (A => X) => (B => Y) => (X ⊗ Y)

  /*    
   * States that SIn = (r Op s1, ..., r Op sn) and SOut = (s1,...,sn)   
   */
  trait LeftMul[Op[_,_], SIn <: Tuple, r, SOut <: Tuple] :
    val r : r 
     
  /*
   * Concatenation relation
   */
  trait ConcatR[T1 <: Tuple, T2 <: Tuple, TOut <: Tuple]

  trait IndexedComonad[C, F <: [X] =>> [Y] =>> Any](using val M : Monoidal[C]) :
    import M._
    def dup[x <: C, y <: C]: F[x ⊗ y] ~> (F[x] ⨀ F[y]) //F[x][F[y][A]]
    def extract : F[I] ~> Id
    def fmap[c<:C, A,B]: F[c][A] => (A => B) => F[c][B]
    def compose[x <: C, y <: C, A, B, X](g : F[y][B] => X, f : F[x][A] => B): F[y ⊗ x][A] => X = 
      { x => g(fmap[y,F[x][A],B](dup[y,x][A](x))(f)) }
    
    

  trait CtxFamily[Sc, El[_,_]] : 
         
    //TODO: transformations between families 
    
    sealed trait Ctx[A <: Tuple, R <: Tuple] :
      //fmap changes the type of a singleton context's variable 
      def fmap[B,C,X<:Sc](f : B => C)(using A =:= Tup1[B], R =:= Tup1[X], Functor[[Y] =>> El[X,Y]]): Ctx[Tup1[C], R]
      //TODO: the paper also demands that for each n, the D^n is an n-functor, i.e., need to generalize fmap to n-ary version! 
      /* Following the coeffect paper, we require only the singleton contexts to be an indexed
         comonad. TODO: should these be rather factored out into a type class? */
      def extract[B](using eq: A =:= Tup1[B], M : Monoidal[Sc])(using R =:= Tup1[M.I]): El[M.I, B]
      //TODO it might be better to have a decomposition judgment Z = X ⊗ Y with R = Tuple1[Z]
      def dup[B,X,Y](using M : Monoidal[Sc])(using A =:= Tup1[B], R =:= Tup1[M.⊗[X,Y]]): Ctx[Tup1[Ctx[A, Tup1[Y]]], Tup1[X]]
      //structural indexed comonad ops
      def dup[r,S <: Tuple](using M : Monoidal[Sc])(using LeftMul[M.⊗, R, r, S]): Ctx[Tup1[Ctx[A,S]], Tup1[r]]
      /*
          Channel[r,A]
          El[r * s,A] ~> El[s, A]
          
          El[r * s1,A1], ..., El[r * sn, An] 
          El[r, El[s1,A1],...,El[sn,An]]
          
          make : (r : Sc) -> A -> El[r.type,A]
          
          r * s for Monoidal[Sc]
          El[r * s, A]
          Tuple1[r * s]
       */
      //(co)lax (semi)monoidal functor ops TODO: better names?
      def m[A2<:Tuple,R2<:Tuple](that : Ctx[A2, R2]): Ctx[Concat[A,A2], Concat[R,R2]]
      def n[A1<:Tuple,A2<:Tuple,R1<:Tuple,R2<:Tuple](using ConcatR[A1,A2,A], ConcatR[R1,R2,R]): (Ctx[A1,R1], Ctx[A2,R2])

    case object CNil extends Ctx[Tup0, Tup0] :
      def fmap[B,C,X<:Sc](f : B => C)(using Tup0 =:= Tup1[B], Tup0 =:= Tup1[X], Functor[[Y] =>> El[X,Y]]): Ctx[Tup1[C], Tup0] = 
        ???
      def extract[B](using eq: Tup0 =:= Tup1[B], M : Monoidal[Sc])(using Tup0 =:= Tup1[M.I]): El[M.I, B] = 
        ???
      def dup[B,X,Y](using M : Monoidal[Sc])(using Tup0 =:= Tup1[B], Tup0 =:= Tup1[M.⊗[X,Y]]): Ctx[Tup1[Ctx[Tup0, Tup1[Y]]], Tup1[X]] = 
        ???
      def dup[r,S <: Tuple](using M : Monoidal[Sc])(using LeftMul[M.⊗, Tup0, r, S]): Ctx[Tup1[Ctx[Tup0,S]], Tup1[r]] =
        ??? //FIXME: this requires constructing a value of type El[r,CNil], need to demand that from El[_,_], also, should El be covariant in the second arg?
      def m[A2<:Tuple,R2<:Tuple](that : Ctx[A2, R2]): Ctx[Concat[Tup0,A2], Concat[Tup0,R2]] = 
        magic(that)
      def n[A1<:Tuple,A2<:Tuple,R1<:Tuple,R2<:Tuple](using ConcatR[A1,A2,Tup0], ConcatR[R1,R2,Tup0]): (Ctx[A1,R1], Ctx[A2,R2]) = 
        magic((CNil, CNil))
  
    case class CCons[A, T <: Tuple, s <: Sc, R <: Tuple](hd : El[s,A], tl : Ctx[T,R]) extends Ctx[A *: T, s *: R] :
      def fmap[B,C,X<:Sc](f : B => C)(using eq1 : (A *: T) =:= Tup1[B], eq2 : (s *: R) =:= Tup1[X], F : Functor[[Y] =>> El[X,Y]]): Ctx[Tup1[C], (s *: R)] = 
        magic(CCons(F.map(magic(hd))(f), CNil))
      def extract[B](using eq: (A *: T) =:= Tup1[B], M : Monoidal[Sc])(using (s *: R) =:= Tup1[M.I]): El[M.I, B] = 
        magic(hd)
      def dup[B,x,y](using M : Monoidal[Sc])(using (A *: T) =:= Tup1[B], (s *: R) =:= Tup1[M.⊗[x,y]]): Ctx[Tup1[Ctx[(A *: T), Tup1[y]]], Tup1[x]] = 
        ??? //FIXME: requires lifting the decomposition of s = x ⊗ y into a decomposition of El[s,A] into El[x,A] and El[y,A]
      def dup[r,S <: Tuple](using M : Monoidal[Sc])(using LeftMul[M.⊗, (s *: R), r, S]): Ctx[Tup1[Ctx[A *: T,S]], Tup1[r]] = 
        ??? //TODO
      def m[A2<:Tuple,R2<:Tuple](that : Ctx[A2, R2]): Ctx[Concat[A *: T,A2], Concat[s *: R,R2]] = 
        ??? //TODO
      def n[A1<:Tuple,A2<:Tuple,R1<:Tuple,R2<:Tuple](using ConcatR[A1,A2,A *: T], ConcatR[R1,R2,s *: R]): (Ctx[A1,R1], Ctx[A2,R2]) = 
        ??? //TODO
  
  //TODO indexed comonad composition of co-kleisli arrows     
    def compose[r<:Sc,s<:Sc,A,B,C](f : Ctx[Tup1[A], Tup1[s]] => B, g : Ctx[Tup1[B], Tup1[r]])(using M : Monoidal[Sc]) : Ctx[Tup1[A], Tup1[M.⊗[r,s]]] => C = ???
  //TODO structural indexed comonad arrow composition  
    def compose[A<:Tuple,S<:Tuple,B,r<:Sc,C,rS<:Tuple](f : Ctx[A,S] => B, g : Ctx[Tup1[B],Tup1[r]] => C)(using M : Monoidal[Sc])(using LeftMul[M.⊗, S, r, rS]): Ctx[A,S] => C = ???
  end CtxFamily   
  
  //def transform[Sc1,El1[_,_],Sc2,El2[_,_]](from : CtxFamily[Sc1,El1], to : CtxFamily[Sc2,El2])
  //f : Sc1 ~> Sc2
  //El[s,A] ~> El2[f(s),A]
  
  
end OMContexts

//TODO the paper "Comonadic Notions of Computation" by Uustalu provides an indexed comonad that has simpler type structure, implement
//that too.

  