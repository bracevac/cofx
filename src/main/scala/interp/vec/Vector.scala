package interp.vec


import scala.annotation.nowarn
import scala.compiletime.ops.int._
import scala.compiletime.ops.boolean._
import scala.compiletime.{summonFrom, error, erasedValue}
import scala.util.NotGiven

object Vectors :
  private[this] def magic[A,B](a : A): B = a.asInstanceOf[B]

  type IntL = Int & Singleton 
  
  type Pred[n <: Int] <: Int = n match
    case S[m] => m

  type NTuple[n<:Int,T] <: Tuple = n match
    case 0   => EmptyTuple
    case n+1 => T *: NTuple[n,T]

  trait Split[l<:Int,r<:Int,res<:Int] :
    val l : l 
    val r : r 
    val res : res 
  
  /*case class NAdd[l <: Nat, r <: Nat, res <:Nat](l : l, r : r, res : res)    
  
  case class NMul[l <: Nat, r <: Nat, res<:Nat](l : l, r : r, res : res)
    
  inline given [r<:Nat] : NAdd[Z.type, r, r] = NAdd(Z,valueOf[r], valueOf[r]) 
  inline given [x<:Nat,y<:Nat,z<:Nat](using rec : NAdd[x,y,z]) : NAdd[Suc[x],y,Suc[z]] = NAdd(Suc(rec.l), rec.r, Suc(rec.res)) 
  
  inline given [r<:Nat] : NMul[Z.type, r, Z.type] = NMul(Z, valueOf[r], Z)
  inline given [x<:Nat] : NMul[Suc[Z.type], x, x] = NMul(Suc(Z), valueOf[x], valueOf[x])
  inline given [x<:Nat,y<:Nat,z<:Nat,w<:Nat](using rec : NMul[x,y,z])(using add : NAdd[z,y,w]) : NMul[Suc[x], y , w] = NMul()*/
  
  
  
  type Within[i, n] <: Int
  transparent inline def checkWithin[i, n] : Within[i,n] =
    inline erasedValue[n] match
      case _: 0    => error("within: n must be nonzero")
      case _: S[m] => inline erasedValue[i] match
        case _ : 0    => magic(1)
        case _ : S[j] => val x = checkWithin[j,m]; magic(1)
        case _        => error("within: could not determine element i")  
      case _        => error("within: could no determine upper bound n")
        
  transparent inline given [i, n] : Within[i,n] = checkWithin[i,n]
  
  sealed trait Vec
  sealed trait Vector[n <: Int, +T] extends Vec :
    //indexed access, fairly limited since i and n must be fully known at compile time
    transparent inline def apply(i : Int): T =
      inline (0 <= i && i < valueOf[n]) match
        case true => unsafeApply(i)
        case false => error("Out of bounds")
    def callable[nn <: IntL](i : Int)(using n <:< nn, Within[i.type,nn]): Unit = ()
    protected[Vectors] def unsafeApply(i : Int): T = ???
    def head(using NotGiven[n =:= 0]): T = ???
    def tail(using NotGiven[n =:= 0]): Vector[Pred[n], T] = ???
    def ++[m <: Int, U >: T](that : Vector[m, U]): Vector[n + m, U]
    def map[U](f : T => U): Vector[n, U]
    def flatMap[m <: Int, U](f: T => Vector[m, U]): Vector[n * m, U]
    def flatten[m<:Int,U](using T <:< Vector[m,U]): Vector[n * m, U] = flatMap(x => magic(x))
    def foldr[U](z : U)(s: (T, U) => U): U
    def foldl[U](z : U)(s: (U, T) => U): U
    def combine[U >: T](using NotGiven[n =:= 0])(f : (U, U) => U): U = tail.foldl(head)(f)
    def zip[U](that: Vector[n,U]): Vector[n,(T,U)]
    def toTuple[U >: T] : NTuple[n,U]
    def extract(using n =:= 1): T
    def dup[i<:Int,j<:Int](using n =:= i * j): Vector[i, Vector[j,T]] 

  case object VNil extends Vector[0, Nothing] :
    def ++[m <: Int, U](that : Vector[m, U]): Vector[0 + m, U] = magic(that)
    def map[U](f : Nothing => U): Vector[0, U] = VNil
    def flatMap[m <: Int, U](f: Nothing => Vector[m, U]): Vector[0 * m, U] = magic(VNil)
    def foldr[U](z : U)(s: (Nothing, U) => U): U = z
    def foldl[U](z : U)(s: (U, Nothing) => U): U = z
    def zip[U](that: Vector[0,U]) = VNil
    def toTuple[U]: NTuple[0, U] = EmptyTuple
    def extract(using 0 =:= 1): Nothing = ???
    /*
     * This shows that we need to be able to analyze i and j and compute the result from that
     * 0,_ => VNil 
     * i,0 => VNil^i      
     */
    def dup[i<:Int,j<:Int](using 0 =:= i * j): Vector[i, Vector[j,Nothing]] = ??? 
    override def toString() : String = "⟨⟩"

  case class VCons[n <: Int, T](hd : T, tl : Vector[n,T]) extends Vector[S[n], T] :
    override protected[Vectors] def unsafeApply(i: Int): T = if (i == 0) then hd else tl.unsafeApply(i)
    override def head(using NotGiven[S[n] =:= 0]): T = hd
    override def tail(using NotGiven[S[n] =:= 0]): Vector[n, T] = magic(tl)
    def ++[m <: Int, U >: T](that : Vector[m, U]): Vector[S[n] + m, U] = magic(VCons(hd, tl ++ that))
    def map[U](f : T => U): Vector[S[n], U] = VCons(f(hd), tl.map(f))
    def flatMap[m <: Int, U](f: T => Vector[m, U]): Vector[S[n] * m, U] = magic(f(hd) ++ tl.flatMap(f))
    def foldr[U](z : U)(s: (T, U) => U): U = s(hd, tl.foldr(z)(s))
    def foldl[U](z : U)(s: (U, T) => U): U = tl.foldl(s(z,head))(s)
    def zip[U](that: Vector[S[n],U]): Vector[S[n],(T,U)] = VCons((hd,that.head), tl.zip(that.tail))
    def toTuple[U >: T]: NTuple[S[n], U] = magic(hd *: tl.toTuple)
    def extract(using S[n] =:= 1): T = hd
    def dup[i<:Int,j<:Int](using S[n] =:= i * j): Vector[i, Vector[j,T]] = ???
    override def toString: String = s"⟨${this.map(_.toString).combine((x,y) => s"${x},${y}")}⟩"

  object Vector :
    /* This reasonably approximates varargs constructors in conjuction with the compiler
     * treating apply((a,b,c)) the same as apply(a,b,c). The issue with ordinary varags
     * is that we cannot easily obtain their length at the type level.
     *
     * Some warts remain. E.g. neither apply() nor apply(()) work, but apply(EmptyTuple).
     * Also, there is no single tupling, apparently.
     * Overloading apply for these corner cases makes the compiler stumble in the n>1 tuple case.
     *
     * Interesting tidbit: if this method is marked transparent, we get a runtime crash
     * (problem is the use of magic).
     */
    inline def apply[T<:Tuple](t : T): Vector[Tuple.Size[T], Tuple.Union[T]] = inline t match
      case EmptyTuple => magic(VNil)
      case t : (_ *: _) => //avoids issue with *:.unapply: https://github.com/lampepfl/dotty/issues/6698
        magic(VCons(t.head, magic(apply(t.tail))))

    //in contrast, this transparent method isn't causing a runtime crash. transparent infers the n singleton correctly,
    //but not always, unfortunately (see mult example below). we probably need a more robust definition principle
    //using implicits
    transparent inline def init[n<:Int,T](n : n, x: T): Vector[n, T] = inline n match
      case 0 => magic(VNil)
      case i => magic(VCons(x, init(i-1, x)))

  object Tests :
    val nil = VNil
    // val nil2 = Vector(())
    //val single = Vector(1)
    val foo : Vector[2,Int] = VCons(1, VCons(2, VNil))
    val bar = foo.head
    val tl = foo.tail
    val baz : Vector[3,Int] = VCons(foo.head, VNil) ++ foo.tail ++ foo.tail
    val x : Vector[2 + 2, Int] = foo ++ foo
    val y : Vector[3 +3 + 2-1-1-2, Int] = x
    val init : Vector[3,Double] = Vector.init(3, 0.0)
    /* these rightfully fail to typecheck
     val fails = nil.head
     val fails2 = nil.tail
     val fails3 : Vector[3,Int] = VCons(1, VCons(2, VNil))
     val fails4 : Vector[5,String] = Vector(1,2,3,4)
     val fails5 = single.combine(_+_)
     */
 
    val access = foo(0)
    //val bad = foo(12)
    val callable = foo.callable(0)
    val callable2 = foo.callable(1)
    //val callable3 = foo.callable(3)
    summon[0 <:< Int]
    summon[0 <:< IntL]
    summon[0 <:< Singleton]
    summon[NotGiven[Int <:< 0]]
    
    val variadic : Vector[4,Int] = Vector(1,2,3,4)
    val variadic2 = Vector(1337,42,4711,0,0xdeadbeef)
    val variadic3 = Vector(1,2.0,"hai")
    val variadic4 : Vector[3,Any] = variadic3
    val variadic5 : Vector[3-1+1*1, Int | Double | String ] = variadic3
    val variadic6 : Vector[3, String | Int | Int | Double | Double ] = variadic5
    val variadic7 : Vector[3, nil.type | Nothing | String | Int | Int | Double | Double ] = variadic5
    val empty = Vector(EmptyTuple)

    val combine = variadic.combine(_+_)
    val comprehension = for {
      i <- variadic
    } yield Vector(i, i, i)
    //unfortunately, the comprehension will choose map and not flatMap
    val comprehension_asc : Vector[12,Int] = comprehension.flatten
    val mult = variadic flatMap { i => Vector(i,i,i) }
    /* this would work, too, but the inferred type is not Vector[12,Int]
       val mult = variadic flatMap { i => Vector(3)(i) } */
    val mult2 : Vector[12,Int] = mult

    val cool : Vector[16,Int] = for {
      i <- variadic
      j <- variadic
    } yield i * j

    @main def run() =
      println(foo)
      println(bar)
      println(tl)
      println(baz)
      println(y)
      println(init)
      println(variadic)
      println(variadic3)
      println(combine)
      println(comprehension)
      println(comprehension_asc)
      println(mult)
      println(cool)
      println(variadic.tail zip variadic3)
      println(cool.toTuple)
      println(access)







