package interp

object Linear :
  infix type |->[-A,+B] = Conversion[A,B] 
  
  //linear types
  enum LType :
    case One
    case ⊸(dom: LType, cod: LType)

  enum Nat :
    case Z
    case S(n : Nat)

  enum NCtx :
    case End(lt: LType)
    case Cons(hd: Option[LType], tl: NCtx)   

  enum Ctx :
    case Empty
    case NEmpty(ctx: NCtx) 

  trait CSingleton[x <: Nat,sigma <: LType, gamma <: Ctx] :
    //functional dependencies
    given singleton    : ((x, sigma) |-> gamma)
    given singleton_inv: (gamma      |-> (x, sigma))

  trait CNSingleton[x <: Nat,sigma <: LType, gamma <: NCtx] :
    //functional dependencies
    given singleton    : ((x, sigma) |-> gamma)
    given singleton_inv: (gamma      |-> (x, sigma))
  
  /*given singletonFromCN[x <: Nat,sigma <: LType, gamma <: NCtx](using cns: CNSingleton[x,sigma,gamma]) : CSingleton[x,sigma,NEmpty(gamma)] with {
    
  }*/
  
  trait CAdd[x <: Nat, sigma <: LType, gamma_in <: Ctx, gamma_out <: Ctx] :
    //functional dependencies
    given add     : ((x, sigma, gamma_in)  |-> gamma_out)
    given add_inv1: ((x, gamma_out)        |-> (gamma_in, sigma ))
    given add_inv2: ((gamma_in, gamma_out) |-> (x, sigma)) 
  
  trait CMerge[gamma1 <: Ctx, gamma2 <: Ctx, gamma3 <: Ctx] :
    //functional dependencies
    given merge     : ((gamma1, gamma2) |-> gamma3) 
    given merge_inv1: ((gamma1, gamma3) |-> gamma2) 
    given merge_inv2: ((gamma2, gamma3) |-> gamma3) 