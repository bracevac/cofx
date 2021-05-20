package interp

import scala.compiletime.{summonFrom, error, erasedValue, summonInline}
import scala.util.NotGiven
/**
 * A study on how to express coeffect scalar splitting at the type and term level.
 */
object DecompNew :


  trait CoeffScalar[C]:

    type zero <: C
    type one <: C

    trait Add[A<:C,B<:C,R<:C]
    trait Mul[A<:C,B<:C,R<:C]
  
  /**  
  trait CoeffScalar[S]:

    type zero <: S
    type one <: S
 
    trait Scalar[S]
    case object ign extends Scalar[zero]
    case object use extends Scalar[one]
    case class Suc(s: S) extends Scalar[S]

    trait Add[A<:S,B<:S,C<:S]
    trait Mul[A<:S,B<:S,C<:S]

    //case class CSAddZ[r<:S]() extends Add[zero, r, r]
    //case class CSAddStep[l <: S, r <: S, res <:S](prev : Add[l,r,res]) extends Add[Suc[l], r, Suc[res]]
  **/

  class NatScalar extends CoeffScalar[Int]:
    type zero = 0
    type one = 1

    case class NAddZ[r <:Int]() extends Add[zero, r, r]
    //case class NAddStep[l <: Int, r <:Int, res <:Int](prev : Add[l,r,res]) extends Add[S[l], r, S[res]]
    //type S not found

  trait Ctx

  trait CoeffShape[C, S, CoeffScalar[C]]:

    type zero <: S
    type one <: S

    def dup(s1: S, s2: S): CoeffShape[C, S, CoeffScalar]
    def extract(s: S): CoeffScalar[C]


end DecompNew
  