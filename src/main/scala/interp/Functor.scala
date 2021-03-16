package interp

import Common._ 

trait Functor[F[_]]:
  extension [A, B](x: F[A])
    def map(f: A => B): F[B]

trait BiFunctor[F[_,_]]:
  extension [A, B, C, D](x: F[A,B])
    def map(f: A => C)(g: B => D) : F[C,D]

given [F[_] : Functor, G[_] : Functor] : BiFunctor[[X,Y] =>> (F[X], G[Y])] with
  extension [A, B, C, D](x: (F[A],G[B]))
    def map(f : A => C)(g: B => D): (F[C],G[D]) = (summon[Functor[F]].map(x._1)(f), summon[Functor[G]].map(x._2)(g))

    
  