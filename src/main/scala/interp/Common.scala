package interp

object Common :
  type ~>[-F[_], +G[_]] = [A] =>  F[A] => G[A]
  type ~~>[-F[_,_], +G[_,_]] = [A,B] => F[A,B] => G[A,B] 
  type ⨀ [F[_], G[_]]   = [X] =>> F[G[X]]
  type Id               = [X] =>> X
  type ×[F[_], G[_]]    = [X] =>> (F[X], G[X])
  type ××[F[_,_], G[_,_]]    = [X,Y] =>> (F[X,Y], G[X,Y])
  