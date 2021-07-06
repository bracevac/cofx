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
        

object Vectors extends App:

    import Scalars._
    import natScalar._

    trait VecIC[n <: Int, +T]:
        
        def take[i<:Int,j<:Int](using Add[i, j, n]): VecIC[i,T]
        def drop[i<:Int,j<:Int](using Add[i, j, n]): VecIC[j,T]
        def dup[i<:Int,j<:Int](using mul : Mul[i,j,n]): VecIC[i, VecIC[j,T]] = mul match
            case _:NMulZLeft[_]        => VNil
            case NMulStep(add, prev)  => VCons(take(using add),drop(using add).dup(using prev))
        //def extract(using NotGiven[n =:= Z.type]): T


    case object VNil extends VecIC[zero, Nothing]: 
        def take[i<:Int,j<:Int](using add : Add[i, j, zero]): VecIC[i,Nothing] = add match
            //Will this work? How do I patttern Match case calss with no parameters
            case _: NAddZ[_] => VNil
        def drop[i<:Int,j<:Int](using add : Add[i, j, zero]): VecIC[j,Nothing] = add match
            case _: NAddZ[_] => VNil
        
    case class VCons[n<:Int,+T](hd : T, tl: VecIC[n,T]) extends VecIC[S[n], T]:
        def take[i<:Int,j<:Int](using add : Add[i,j,S[n]]): VecIC[i,T] = add match 
            case _: NAddZ[_] => VNil
            case NAddStep(prev) => VCons(hd, tl.take(using prev))
        def drop[i<:Int,j<:Int](using add : Add[i,j,S[n]]): VecIC[j,T] = add match
            case _: NAddZ[_] => this
            case NAddStep(prev) => tl.drop(using prev)
    
    
    type one = 1
    type i = Int
    summon[one <:< i]
    //summon[VecIC[one, Nothing] <:< VecIC[i, Nothing]]
    
    

    class BnReuseShape extends IndexedComonad[Int, VecIC]:
        def dup[i <: Int, j<: Int, n <: Int, T](d: VecIC[n, T])(using mul: this.s.Mul[i, j, n]): VecIC[i, VecIC[j, T]] = mul match
            case _: NMulZLeft[_]      => VNil
            case NMulStep(add, prev)  => VCons(d.take(using add),d.drop(using add).dup(using prev))
        def extract[n <: Int, T](d: VecIC[n, T])(using NotGiven[n =:= this.s.zero]): T = ???
        def map[n <: Int, A, B](d: VecIC[n, A], f: A => B): VecIC[n, B] = ???