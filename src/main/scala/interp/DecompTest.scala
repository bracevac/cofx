package interp

import scala.compiletime.{summonFrom, error, erasedValue, summonInline}
import scala.util.NotGiven
import scala.compiletime.ops.int._
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
    case class NAddStep[l <: Int, r <:Int, res <:Int](prev : Add[l,r,res]) extends Add[S[l], r, S[res]]
    trait NAddLvl1 :
      given addz[r<:Int] : Add[zero,r,r] = NAddZ()

    object NAdd extends NAddLvl1 :
      given addstep[l <: Int, r <:Int, res <:Int](using prev : Add[l,r,res]) : Add[S[l],r,S[res]] = NAddStep(prev)
    
    case class NMulZLeft[r <:Int]() extends Mul[zero, r, zero]
    case class NMulZRight[l <: Int]() extends Mul[S[l], zero, zero]
    case class NMulStep[l <: Int, r <:Int, res <:Int, sum <:Int](add : Add[S[r],res,sum], prev : Mul[l,S[r],res]) extends Mul[S[l],S[r],sum]
    
    trait NMulLvl2 :
      given mulzl[r <: Int] : Mul[zero, r, zero] = NMulZLeft()
    trait NMulLvl1 extends NMulLvl2 :
      given mulzr[l <: Int] : Mul[S[l],zero,zero] = NMulZRight()
    object NMul extends NMulLvl1 :
      given mulstep[l <: Int, r <:Int, res <:Int, sum <:Int](using prev : Mul[l,S[r],res], add : Add[S[r],res,sum]) : Mul[S[l],S[r],sum] = NMulStep(add,prev)

  trait Ctx

  /* S: 
  trait CoeffShape[S, C]:

    type zero <: S
    type one <: S

    def dup[C](using CoeffScalar[C].Add): CoeffShape[S]
    //def extract(s: S): CoeffScalar[C]*/


end DecompNew
  