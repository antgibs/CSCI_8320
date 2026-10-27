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

predicate LessAlt(x: Unary, y: Unary) {
  y != Zero && (x == Zero || Less(x.pred, y.pred))
}

lemma LessSame(x: Unary, y: Unary)
  ensures Less(x, y) == LessAlt(x, y)
{
}

lemma LessCorrect(x: Unary, y: Unary)
  ensures Less(x, y) <==> UnaryToNat(x) < UnaryToNat(y)
{
}

lemma LessTransitive(x: Unary, y: Unary, z: Unary)
  requires Less(x, y) && Less(y, z)
  ensures Less(x, z)
{
}

/* Exercise 7.3 below */

lemma {:induction false} LessTrichotomous(x: Unary, y: Unary)
  ensures  (Less(x,y) && !(x==y) && !(Less(y,x)))       // x < y exlusively 
        || ((x == y) && !(Less(x,y)) && !(Less(y,x)))   // x == y excluively
        || (Less(y,x) && !(Less(x,y) && !(x==y)))       // y < x  exclusively
{
    match x
    case Zero =>    // x has become Zero while y > 0
    case Suc(x') => // x is not Zero
        match y
        case Zero =>    // y is Zero while x > 0
        case Suc(y') => LessTrichotomous(x', y'); // use lemma recursively to ultimately find out whether x > y, y > x, or x = y
}