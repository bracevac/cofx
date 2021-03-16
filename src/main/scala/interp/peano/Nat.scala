package interp.peano

import scala.compiletime.ops.int._
import scala.compiletime.{summonFrom, error, erasedValue, S, summonInline}
import scala.util.NotGiven

object Nat :
  sealed trait Nat :
    def toInt : Int
    override def toString() = s"[${this.toInt}]"
  case object Z extends Nat :
    def toInt = 0
  case class Suc[N <: Nat](n : N) extends Nat :
    def toInt = n.toInt + 1

  type _0 = Z.type
  val  _0 = Z
  type _1 = Suc[_0]
  val  _1 = Suc(_0)
  type _2 = Suc[_1]
  val  _2 = Suc(_1)
  type _3 = Suc[_2]
  val  _3 = Suc(_2)
  type _4 = Suc[_3]
  val  _4 = Suc(_3)
  type _5 = Suc[_4]
  val  _5 = Suc(_4)
  type _6 = Suc[_5]
  val  _6 = Suc(_5)

  type nat[i <: Int] <: Nat = i match
    case 0    => Z.type
    case S[n] => Suc[nat[n]]
  transparent inline def nat[i<:Int]: nat[i] =
    inline erasedValue[i] match
      case _:0 => Z
      case _:S[n] => Suc(nat[n])
  
  type int[n <: Nat] <: Int = n match 
    case Z.type => 0
    case Suc[n] => 1+int[n]
  transparent inline def int[n<:Nat]: Int =
    inline erasedValue[n] match
      case _:Z.type => 0
      case _:Suc[n] => 1+int[n] 
  
  given Z.type = Z
  given [n<:Nat](using n: n): Suc[n] = Suc(n)
 
end Nat