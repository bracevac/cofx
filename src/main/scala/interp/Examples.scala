package interp

import DecompNew._
import scala.compiletime.ops.int._
import scala.util.NotGiven
import scala.compiletime.{summonFrom, error, erasedValue, summonInline}


object Scalars: 

    implicit object natScalar extends CoeffScalar[Int]:
        type use = 0
        type ign = 1

        type zero = use

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
        

    implicit object testScalar extends CoeffScalar[Int]
    
    implicit object boolScalar extends CoeffScalar[Boolean]:
        type use = false
        type ign = true

        case object BAddFalseFalse extends Add[false, false, false]
        case object BAddFalseTrue extends Add[false, true, false]
        case object BAddTrueFalse extends Add[true, false, false]
        case object BAddTrueTrue extends Add[true, true, true]

        case object BMulTrueTrue extends Mul[true, true, true]
        case object BMulTrueFalse extends Mul[true, false, true]
        case object BMulFalseTrue extends Mul[false, true, true]
        case object BMulFalse extends Mul[false, false, false]

end Scalars

object Vectors extends App:

    import Scalars._

    object Vector:

        import natScalar._

        trait IVector[n <: Int, +T]:
            def take[i<:Int,j<:Int](using Add[i, j, n]): IVector[i,T]
            def drop[i<:Int,j<:Int](using Add[i, j, n]): IVector[j,T]

        case object VNil extends IVector[use, Nothing]: 
            def take[i<:Int,j<:Int](using add : Add[i, j, use]): IVector[i,Nothing] = add match
                case NAddZ() => VNil
            def drop[i<:Int,j<:Int](using add : Add[i, j, use]): IVector[j,Nothing] = add match
                case NAddZ() => VNil
            
        case class VCons[n<:Int,+T](hd : T, tl: IVector[n,T]) extends IVector[S[n], T]:
            def take[i<:Int,j<:Int](using add : Add[i,j,S[n]]): IVector[i,T] = add match 
                case NAddZ() => VNil
                case NAddStep(prev) => VCons(hd, tl.take(using prev))
            def drop[i<:Int,j<:Int](using add : Add[i,j,S[n]]): IVector[j,T] = add match
                case NAddZ() => this
                case NAddStep(prev) => tl.drop(using prev)
    
    
    class BnReuseShape extends IndexedComonad[Int, Vector.IVector, natScalar.type](using natScalar):
        import s._
        def dup[i <: Int, j<: Int, n <: Int, T](d: Vector.IVector[n, T])(using mul: this.s.Mul[i, j, n]): Vector.IVector[i, Vector.IVector[j, T]] = mul match
            case NMulZLeft()          => Vector.VNil
            case NMulStep(add, prev)  => Vector.VCons(d.take(using add), dup(d.drop(using add))(using prev))
        def extract[n <: Int, T](d: Vector.IVector[n, T])(using NotGiven[n =:= this.s.use]): T = d match
            case Vector.VCons(hd, tl) => hd
        def map[n <: Int, A, B](d: Vector.IVector[n, A], f: A => B): Vector.IVector[n, B] = d match
            case Vector.VNil          => Vector.VNil
            case Vector.VCons(hd, tl) => Vector.VCons(f(hd), map(tl, f))

    /**
    trait PH[n <: Boolean, T]
    class LivenessShape extends IndexedComonad[Boolean, PH, boolScalar.type](using boolScalar):
        def dup[i <: Boolean, j <: Boolean, n <: Boolean, T](d: PH[n, T])(using s.Mul[i, j, n]): PH[i, PH[j, T]] = ???
        def extract[n <: Boolean, T](d : PH[n,T])(using NotGiven[n =:= s.use]): T = ???
        def map[n <: Boolean, A, B](d : PH[n,A], f : A => B) : PH[n,B] = ???
    **/
end Vectors

    
  
object Context extends App:

    import Scalars.natScalar

    class Nat extends ScalarMul[Int]

    

end Context
    /**
     * We need to change naming of scalar and indexedcomoonad traits since they're BnReuse specific
     * The n>0 in Ctx is still an issue (so are negative integers) - right ADT for non-zero in a utils file
     * PH placeholder for boolean shape
     * 
     * Coeffect[Int] => A, B
     * VecIC => natScalar
     * BnReuseShape(B) {
     *  VecIC[A]
     * }
     **/
