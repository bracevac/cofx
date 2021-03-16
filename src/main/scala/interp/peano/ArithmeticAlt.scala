package interp.peano

import scala.compiletime.{summonFrom, error, erasedValue}

object ArithmeticAlt :
  private[this] def magic[A,B](a : A): B = a.asInstanceOf[B]

  import Nat._
  
  sealed trait NAdd[l <: Nat, r <: Nat, res <:Nat]
  
  /*
   * ---------[NAddZ]
   * 0 + r = r
   */
  case class NAddZ[r<:Nat]() extends NAdd[Z.type, r, r]

  /*
   * l + r = res
   * ---------------------[NAddStep]
   * Suc(l) + r = Suc(res)
   */
  case class NAddStep[l <: Nat, r <: Nat, res <:Nat](prev : NAdd[l,r,res]) extends NAdd[Suc[l], r, Suc[res]]
  /*
   * Prioritize the resolution rules
   */
  trait NAddLvl1 :
    //it's easier to read the error traces of implicit resolution if the givens have names
    given addz[r<:Nat] : NAdd[Z.type,r,r] = NAddZ()
  /*
   * Clients that are oblivious to the proof structure may just extract the factors.
   */
  object NAdd extends NAddLvl1 :
    given addstep[l<:Nat,r<:Nat,res<:Nat](using prev : NAdd[l,r,res]) : NAdd[Suc[l],r,Suc[res]] = NAddStep(prev)
  
  sealed trait NMul[l <: Nat, r <: Nat, res<:Nat]
  /*
   * ---------[NMulZLeft]
   * 0 * r = 0
   */
  case class NMulZLeft[r <: Nat]() extends NMul[Z.type, r, Z.type]
  /*
   * ---------[NMulZRight]
   * Suc[l] * 0 = 0
   */
  case class NMulZRight[l <: Nat]() extends NMul[Suc[l], Z.type, Z.type]
  /*
   * l * r = res    r + res = sum
   * ----------------------------[NMulStep]
   * Suc(l) * r = sum
   */
  case class NMulStep[l<:Nat,r<:Nat,res<:Nat,sum<:Nat](add : NAdd[Suc[r],res,sum], prev : NMul[l,Suc[r],res]) extends NMul[Suc[l],Suc[r],sum]

  trait NMulLvl2 :
    given mulzl[r <: Nat] : NMul[Z.type, r, Z.type] = NMulZLeft()
  trait NMulLvl1 extends NMulLvl2 :
    given mulzr[l <: Nat] : NMul[Suc[l],Z.type,Z.type] = NMulZRight()
  object NMul extends NMulLvl1 :
    given mulstep[l<:Nat,r<:Nat,res<:Nat,sum<:Nat](using prev : NMul[l,Suc[r],res], add : NAdd[Suc[r],res,sum]) : NMul[Suc[l],Suc[r],sum] = NMulStep(add,prev)

  import scala.compiletime.ops.int._
  type Sum[l<:Nat,r<:Nat] <: Nat = l match
    case Z.type => r
    case Suc[n] => Suc[Sum[n,r]]
  type Subtract[r<:Nat,sum<:Nat] <: Nat = (r,sum) match
    case (Z.type, _)    => sum 
    case (Suc[n],Suc[m]) => Subtract[n,m]
  type Mul[l<:Nat,r<:Nat] <: Nat = l match 
     case Z.type => nat[0 * Nat.int[r]]
     case Suc[n] => nat[Nat.int[Suc[n]] * Nat.int[r]]
  type Div[l<:Nat,prod<:Nat] <: Nat = l match
    case Suc[n] => nat[Nat.int[Suc[n]] / Nat.int[prod]]
  
  private[this] inline def unsafesumev[l<:Nat]: Any =
    inline erasedValue[l] match
      case _:Z.type => NAddZ()
      case _:Suc[n] =>
        val prev = unsafesumev[n]
        NAddStep(magic(prev))
  inline def sumev[l<:Nat,r<:Nat]: NAdd[l,r,Sum[l,r]] = magic(unsafesumev[l])

  private[this] inline def unsafeprodev[l<:Nat,r<:Nat]: Any =
    inline erasedValue[l] match
      case _:Z.type => NMulZLeft()
      case _: Suc[n] => inline erasedValue[r] match
        case _: Z.type => NMulZRight()
        case _: Suc[m] =>
          val prev = unsafeprodev[n,r]
          val s    = unsafesumev[r]
          NMulStep(magic(s),magic(prev))
  inline def prodev[l<:Nat,r<:Nat]: NMul[l,r,Mul[l,r]] = magic(unsafeprodev[l,r])
  
  private[this] inline def unsafesummandl[r<:Nat,sum<:Nat] : Any =
    inline erasedValue[(r,sum)] match
      case _:(Z.type,_)      => unsafesumev[sum]
      case _:(Suc[n],Suc[m]) => NAddStep(magic(unsafesummandl[n,m])) 
  inline def summandl[r<:Nat,sum<:Nat]: NAdd[Subtract[r,sum],r,sum] = magic(unsafesummandl[r,sum])  
  inline def summandr[l<:Nat,sum<:Nat]: NAdd[l,Subtract[l,sum], sum] = magic(unsafesumev[l])
  
  private[this] inline def eq[n<:Nat,m<:Nat] : Unit = 
    inline erasedValue[(n,m)] match
      case _:(Z.type,Z.type) => ()
      case _:(Suc[n],Suc[m]) => eq[n,m] 
  
  @main def peanoAltTests() =
    val tests = List(
      prodev[_3,_3],
      sumev[_3,_3],
      prodev[nat[3],nat[9]],
      prodev[nat[9],nat[9]],
      summandl[nat[3],nat[6]],
      summandr[nat[2],nat[8]]
    )
    val a : NMul[_3,_3,nat[9]] = prodev[_3,_3]
    val b : NAdd[_3,_3,_6] = sumev[_3,_3]
    val c : NMul[nat[3],nat[9],nat[27]] = prodev[nat[3],nat[9]] 
    val d : NAdd[nat[2],nat[6],nat[8]] = summandr[nat[2],nat[8]]
    val twentyseven : Mul[nat[3],nat[9]] = nat[27] 
    tests.foreach(println(_))
    
end ArithmeticAlt
