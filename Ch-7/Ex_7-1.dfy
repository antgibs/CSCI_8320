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
        match x         // The value of x doesn't strictly matter for determining the ultimate truth value, but each constructor of x need its own match case
        case Zero => true   // (x = Zero and y != 0) => x is less than y
        case Suc(_) => Less'(x.pred, y.pred)
}

/* Prove that Less` == Less */

lemma {:induction false} Less'Less(x: Unary, y: Unary)
  ensures Less'(x,y) <==> Less(x,y)
{
    match y
    case Zero => // (y != Zero) == false for both predicates; biconditional holds
    case Suc(y') =>
        match x
        case Zero => // (x.Suc?) == false for both predicates; truth value relies on (y != Zero)
            calc
            {
                Less'(Zero,y);
                <==> // def. Less'(Zero, y)
                true;
                <==> // def. Less(Zero, y)
                Less(Zero, y);
            }
        case Suc(x') => 
            calc
            {
                Less'(x,y);
                <==> // def. Less'
                Less'(x', y');
                <==> { Less'Less(x', y'); }
                Less(x', y');
                <==>
                Less(x,y);
            }
            
}