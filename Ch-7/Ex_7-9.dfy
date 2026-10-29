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

lemma LessTrichotomous(x: Unary, y: Unary)
  // 1 or 3 of them are true:
  ensures Less(x, y) <==> x == y <==> Less(y, x)
  // not all 3 are true:
  ensures !(Less(x, y) && x == y && Less(y, x))
{
}

function Add(x: Unary, y: Unary): Unary {
  match y
  case Zero => x
  case Suc(y') => Suc(Add(x, y'))
}

lemma {:induction false} AddCorrect(x: Unary, y: Unary)
  ensures UnaryToNat(Add(x, y)) == UnaryToNat(x) + UnaryToNat(y)
{
  match y
  case Zero =>
  case Suc(y') =>
    calc {
      UnaryToNat(Add(x, y));
    ==  // y == Suc(y')
      UnaryToNat(Add(x, Suc(y')));
    ==  // def. Add
      UnaryToNat(Suc(Add(x, y')));
    ==  // def. UnaryToNat
      1 + UnaryToNat(Add(x, y'));
    ==  { AddCorrect(x, y'); }
      1 + UnaryToNat(x) + UnaryToNat(y');
    ==  // def. UnaryToNat
      UnaryToNat(x) + UnaryToNat(Suc(y'));
    ==  // y == Suc(y')
      UnaryToNat(x) + UnaryToNat(y);
    }
}

lemma {:induction false} SucAdd(x: Unary, y: Unary)
  ensures Suc(Add(x, y)) == Add(Suc(x), y)
{
  match y
  case Zero =>
  case Suc(y') =>
    calc {
      Suc(Add(x, Suc(y')));
    ==  // def. Add
      Suc(Suc(Add(x, y')));
    ==  { SucAdd(x, y'); }
      Suc(Add(Suc(x), y'));
    ==  // def. Add
      Add(Suc(x), Suc(y'));
    }
}

lemma {:induction false} AddZero(x: Unary)
  ensures Add(Zero, x) == x
{
  match x
  case Zero =>
  case Suc(x') =>
    calc {
      Add(Zero, Suc(x'));
    ==  // def. Add
      Suc(Add(Zero, x'));
    ==  { AddZero(x'); }
      Suc(x');
    }
}

function Sub(x: Unary, y: Unary): Unary
  requires !Less(x, y)
{
  match y
  case Zero => x
  case Suc(y') => Sub(x.pred, y')
}

lemma SubCorrect(x: Unary, y: Unary)
  requires !Less(x, y)
  ensures UnaryToNat(Sub(x, y)) == UnaryToNat(x) - UnaryToNat(y)
{
}

/* 
Exercise 7.9 below
Write suitable condition for AddSub
*/

lemma AddSub(x: Unary, y: Unary)
  requires !Less(x, y) // Applies the precondition of Sub to an Add that contains a Sub
  ensures Add(Sub(x, y), y) == x
{}