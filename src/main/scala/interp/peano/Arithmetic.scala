package interp.peano

import scala.compiletime.{summonFrom, error, erasedValue, summonInline}
import scala.util.NotGiven

object Arithmetic :
  
  import Nat._ 

  /*
   * Design pattern: define a calculus for a relation in terms of a GADT modeling the
   * derivation trees. Metavariables become (phantom) type variables of the relation's root class. 
   * The GADT can be analyzed by implementations. How the derivations are *calculated* is subject
   * to the implicit resolution, which is an orthogonal layer. 
   */
  sealed trait NAddRoot
  sealed trait NAdd[l <: Nat, r <: Nat, res <:Nat] extends NAddRoot :
    val l   : l
    val r   : r
    val res : res
    override def toString() = s"$l + $r = $res"

  /* 
   * ---------[NAddZ]
   * 0 + r = r
   */
  case class NAddZ[r<:Nat](r:r) extends NAdd[Z.type, r, r] :
    val l   = Z
    val res = r

  /* 
   * l + r = res
   * ---------------------[NAddStep]
   * Suc(l) + r = Suc(res)
   */
  case class NAddStep[l <: Nat, r <: Nat, res <:Nat](prev : NAdd[l,r,res]) extends NAdd[Suc[l], r, Suc[res]] :
    val l   = Suc(prev.l)
    val r   = prev.r
    val res = Suc(prev.res)

  /*
   * Prioritize the resolution rules
   */
  trait NAddLvl1 :
    //it's easier to read the error traces of implicit resolution if the givens have names 
    given addz[r<:Nat](using r:r) : NAdd[Z.type,r,r] = NAddZ(r)
  /*
   * Clients that are oblivious to the proof structure may just extract the factors.  
   */
  object NAdd extends NAddLvl1 :
    def unapply[l<:Nat,r<:Nat,res<:Nat](add: NAdd[l,r,res]): (l,r,res) = (add.l,add.r,add.res)
    given addstep[l<:Nat,r<:Nat,res<:Nat](using prev : NAdd[l,r,res]) : NAdd[Suc[l],r,Suc[res]] = NAddStep(prev)

  /*
   * Functional dependencies for NAdd
   */
  trait SumOf[l<:Nat,r<:Nat] :
    type sum <: Nat
    val evidence : NAdd[l,r,sum]
  given [l0<:Nat,r0<:Nat,out<:Nat](using sum : NAdd[l0,r0,out]) : SumOf[l0,r0] with {
    type sum = out
    val evidence = sum
  }
  trait SummandR[l<:Nat,sum<:Nat] :
    type r <: Nat
    val evidence : NAdd[l,r,sum]
  given [l0<:Nat,r0<:Nat,out<:Nat](using sum : NAdd[l0,r0,out]) : SummandR[l0,out] with {
    type r = r0
    val evidence = sum
  }
  trait SummandL[r<:Nat,sum<:Nat] :
    type l <: Nat
    val evidence : NAdd[l,r,sum]
  given [l0<:Nat,r0<:Nat,out<:Nat](using sum : NAdd[l0,r0,out]) : SummandL[r0,out] with {
    type l = l0
    val evidence = sum
  }

  sealed trait NMul[l <: Nat, r <: Nat, res<:Nat] :
    val l   : l
    val r   : r
    val res : res
    override def toString() = s"$l * $r = $res"

  /*
   * ---------[NMulZLeft]
   * 0 * r = 0
   */
  case class NMulZLeft[r <: Nat](r : r) extends NMul[Z.type, r, Z.type] :
    val l   = Z
    val res = Z

  /*
   * l * r = res    r + res = sum
   * ----------------------------[NMulStep] 
   * Suc(l) * r = sum
   */
  case class NMulStep[l<:Nat,r<:Nat,res<:Nat,sum<:Nat](prev : NMul[l,r,res], add : NAdd[r,res,sum]) extends NMul[Suc[l],r,sum] :
    val l   = Suc(prev.l)
    val r   = prev.r
    val res = add.res

  trait NMulLvl1 :
    given mulz[r <: Nat](using r : r) : NMul[Z.type, r, Z.type] = NMulZLeft(r)
  object NMul extends NMulLvl1 :
    def unapply[l<:Nat,r<:Nat,res<:Nat](mul: NMul[l,r,res]): (l,r,res) = (mul.l,mul.r,mul.res)
    given mulstep[l<:Nat,r<:Nat,res<:Nat,sum<:Nat](using add : NAdd[r,res,sum], prev : NMul[l,r,res]) : NMul[Suc[l],r,sum] = NMulStep(prev,add)
  
  /*   
   * Functional dependencies for NMul 
   */
  trait ProductOf[l<:Nat,r<:Nat] :
    type prod <: Nat
    val evidence : NMul[l,r,prod]
  given [l0<:Nat,r0<:Nat,out<:Nat](using mul : NMul[l0,r0,out]) : ProductOf[l0,r0] with 
    type prod = out
    val evidence = mul
  
  trait FactorR[l<:Nat,out<:Nat] :
    type r <: Nat
    val evidence : NMul[l,r,out]
  given [l0<:Nat,r0<:Nat,out<:Nat](using mul : NMul[l0,r0,out]) : FactorR[l0,out] with 
    type r = r0
    val evidence = mul
  
  trait FactorL[r<:Nat,out<:Nat] :
    type l <: Nat
    val evidence : NMul[l,r,out]
  given [l0<:Nat,r0<:Nat,out<:Nat](using mul : NMul[l0,r0,out]) : FactorL[r0,out] with 
    type l = l0
    val evidence = mul

end Arithmetic
