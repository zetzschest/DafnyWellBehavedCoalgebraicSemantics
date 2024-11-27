module Expressions {

  /* Definitions */

  datatype Exp<A> = Zero | One | Char(A) | Plus(Exp, Exp) | Comp(Exp, Exp) | Star(Exp)

  function Eps<A>(e: Exp): bool {
    match e
    case Zero => false
    case One => true
    case Char(a) => false
    case Plus(e1, e2) => Eps(e1) || Eps(e2)
    case Comp(e1, e2) => Eps(e1) && Eps(e2)
    case Star(e1) => true
  }

  function Delta<A(==)>(e: Exp): A -> Exp {
    (a: A) =>
      match e
      case Zero => Zero
      case One => Zero
      case Char(b) => if a == b then One else Zero
      case Plus(e1, e2) => Plus(Delta(e1)(a), Delta(e2)(a))
      case Comp(e1, e2) => Plus(Comp(Delta(e1)(a), e2), Comp(if Eps(e1) then One else Zero, Delta(e2)(a)))
      case Star(e1) => Comp(Delta(e1)(a), Star(e1))
  }

}
