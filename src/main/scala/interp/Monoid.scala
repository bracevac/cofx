package interp

trait SemiGroup[T]:
  extension (x: T)
    infix def ++(y: T): T

trait Monoid[T] extends SemiGroup[T]:
  def unit: T
