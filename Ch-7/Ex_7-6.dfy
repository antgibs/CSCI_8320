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

/*
Exercise 7.6 Below
Prove that Add is associative
*/

lemma {:induction false} AddAssociative(x: Unary, y: Unary, z: Unary)
ensures Add(Add(x,y),z) == Add(x, Add(y,z))
{
    match x
    case Zero => { AddZero(y); } { AddZero((Add(y,z))); }  // Add(Add(Zero,y),z) == Add(Zero, Add(y,z)) == Add(y,z)
    case Suc(x') =>
        match z
        case Zero => 
        case Suc(z') =>
            match y
            case Zero =>
                calc
                {
                    Add(Add(x, Zero),z);
                    == { AddZero(x); }
                    Add(x,z);
                    == { AddZero(z); }
                    Add(x, Add(Zero, z));
                }
            case Suc(y') =>
                calc
                {
                    Add(Add(x,y), z);
                    == // def. Add(x,y)
                    Add(Suc(Add(x, y')), z);
                    == { SucAdd(Add(x, y'), z); } // Shift Successor function outside
                    Suc(Add(Add(x, y'), z));
                    == { AddAssociative(x, y', z);} // Move inner Add from (x,y') to (y',z)
                    Suc(Add(x, Add(y', z)));
                    == { SucAdd(x, Add(y', z)); } // Shift Successor function into outer Add function
                    Add(x, Suc(Add(y', z)));      // Successor function distributes to second argument of Add function
                    == { SucAdd(y', z); }         // Move Successor function onto y'
                    Add(x, Add(Suc(y'), z));      // Dafny was smart enough to complete the calculation without this line
                    == // y = Suc(y')
                    Add(x, Add(y, z));
                }
}