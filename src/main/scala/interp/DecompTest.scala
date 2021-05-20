package interp

import scala.compiletime.{summonFrom, error, erasedValue, summonInline}
import scala.util.NotGiven
/**
 * A study on how to express coeffect scalar splitting at the type and term level.
 */
object DecompNew :

  /**
  trait CoeffScalar[S]:

    type zero <: S
    type one <: S

    trait Add[A<:S,B<:S,C<:S]
    trait Mul[A<:S,B<:S,C<:S]
  **/
    
  trait CoeffScalar[S]:

    type zero <: S
    type one <: S
 
    trait Scalar[S]
    case object ign extends Scalar[zero]
    case object use extends Scalar[one]
    case class Suc(s: S) extends Scalar[S]

    trait Add[A<:S,B<:S,C<:S]
    trait Mul[A<:S,B<:S,C<:S]

    case class CSAddZ[r<:S]() extends Add[zero, r, r]
    case class CSAddStep[l <: S, r <: S, res <:S](prev : Add[l,r,res]) extends Add[Suc[l], r, Suc[res]]

end DecompNew
  