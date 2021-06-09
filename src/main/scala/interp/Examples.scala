package interp

import DecompNew._
import scala.compiletime.ops.int._

object Scalars: 

    object NatScalar extends CoeffScalar[Int]:
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
        

object Vectors:

    class VecIC[n <: Int, T]:
        def toString = ???
    import Scalars._
    summon[CoeffScalar[Int]]
    class BnReuseShape extends IndexedComonad[Int, BnReuseIC]
