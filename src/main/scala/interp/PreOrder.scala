package interp

trait PreOrder[T] :
  extension (x : T) 
    infix def ≤(that : T): Boolean
