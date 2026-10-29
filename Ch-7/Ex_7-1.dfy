datatype Unary = Zero | Suc(pred: Unary)

function UnaryToNat(x: Unary): nat {
  match x
  case Zero => 0
  case Suc(x') => 1 + UnaryToNat(x')
}

function NatToUnary(n: nat): Unary {
  if n == 0 then Zero else Suc(NatToUnary(n-1))
}

lemma NatUnaryCorrespondence(n: nat, x: Unary)
  ensures UnaryToNat(NatToUnary(n)) == n
  ensures NatToUnary(UnaryToNat(x)) == x
{
}

predicate Less(x: Unary, y: Unary) {
  y != Zero && (x.Suc? ==> Less(x.pred, y.pred))
}

/* 
Exercise 7.1 below
*/

/* Write Less' using a matach expression */

predicate Less'(x: Unary, y: Unary)
{
    match y
    case Zero => false
    case Suc(_) =>      // y != Zero
        match x
        case Zero => false
        case Suc(_) =>  // x.Suc? == true
            Less'(x.pred, y.pred)
}

