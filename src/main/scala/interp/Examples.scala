package interp

import DecompNew._
import scala.compiletime.ops.int._
import scala.util.NotGiven
import scala.compiletime.{summonFrom, error, erasedValue, summonInline}


object Scalars: 

    implicit object natScalar extends CoeffScalar[Int]:
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
        

    implicit object boolScalar extends CoeffScalar[Boolean]:
        type zero = false
        type one = true

        case object BAddFalseFalse extends Add[false, false, false]
        case object BAddFalseTrue extends Add[false, true, false]
        case object BAddTrueFalse extends Add[true, false, false]
        case object BAddTrueTrue extends Add[true, true, true]

        case object BMulTrueTrue extends Mul[true, true, true]
        case object BMulTrueFalse extends Add[true, false, true]
        case object BMulFalseTrue extends Add[false, true, true]
        case object BMulFalse extends Mul[false, false, false]



object Vectors extends App:

    import Scalars._

    trait VecIC[n <: Int, +T]:
        import natScalar._
        def take[i<:Int,j<:Int](using Add[i, j, n]): VecIC[i,T]
        def drop[i<:Int,j<:Int](using Add[i, j, n]): VecIC[j,T]
        //def extract(using NotGiven[n =:= Z.type]): T


    case object VNil extends VecIC[natScalar.zero, Nothing]: 
        import natScalar._
        def take[i<:Int,j<:Int](using add : Add[i, j, zero]): VecIC[i,Nothing] = add match
            case NAddZ() => VNil
        def drop[i<:Int,j<:Int](using add : Add[i, j, zero]): VecIC[j,Nothing] = add match
            case NAddZ() => VNil
        
    case class VCons[n<:Int,+T](hd : T, tl: VecIC[n,T]) extends VecIC[S[n], T]:
        import natScalar._
        def take[i<:Int,j<:Int](using add : Add[i,j,S[n]]): VecIC[i,T] = add match 
            case NAddZ() => VNil
            case NAddStep(prev) => VCons(hd, tl.take(using prev))
        def drop[i<:Int,j<:Int](using add : Add[i,j,S[n]]): VecIC[j,T] = add match
            case NAddZ() => this
            case NAddStep(prev) => tl.drop(using prev)
    

    class BnReuseShape extends IndexedComonad[Int, VecIC, natScalar.type](using natScalar):
        import s._
        def dup[i <: Int, j<: Int, n <: Int, T](d: VecIC[n, T])(using mul: this.s.Mul[i, j, n]): VecIC[i, VecIC[j, T]] = mul match
            case NMulZLeft()          => VNil
            case NMulStep(add, prev)  => VCons(d.take(using add), dup(d.drop(using add))(using prev))
        def extract[n <: Int, T](d: VecIC[n, T])(using NotGiven[n =:= this.s.zero]): T = d match
            case VCons(hd, tl) => hd
        def map[n <: Int, A, B](d: VecIC[n, A], f: A => B): VecIC[n, B] = d match
            case VNil          => VNil
            case VCons(hd, tl) => VCons(f(hd), map(tl, f))
    
    trait PH[n <: Boolean, T]
    class LivenessShape extends IndexedComonad[Boolean, PH, boolScalar.type](using boolScalar):
        def dup[i <: Boolean, j <: Boolean, n <: Boolean, T](d: PH[n, T])(using s.Mul[i, j, n]): PH[i, PH[j, T]] = ???
        def extract[n <: Boolean, T](d : PH[n,T])(using NotGiven[n =:= s.zero]): T = ???
        def map[n <: Boolean, A, B](d : PH[n,A], f : A => B) : PH[n,B] = ???

    
    
    /**
     * Why not case class NAddZ?
     * Is this structure good? THe way logic is spread?
     * Ctx is common across all? Should I have a single Ctx trait and no inhertiance of it?
     * Does every variable have live or dead state, is there any null?
     * We need to change naming of scalar and indexedcomoonad traits since they're BnReuse specific
     * Case class the truth table or just four objects each?
     * You could pass a bad D into IndexedComonad because it doesn't have to match the same COeffect[S] it uses internally
     * The n>0 in Ctx is still an issue (so are negative integers) 
     * PH placeholder for boolean shape
     **/
