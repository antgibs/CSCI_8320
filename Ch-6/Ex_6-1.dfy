datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat {
  match xs
  case Nil => 0
  case Cons(_, tail) => 1 + Length(tail)
}

function Length'<T>(xs: List<T>): nat {
  if xs == Nil then 0 else 1 + Length'(xs.tail)
}

lemma LengthIsLength'<T>(xs: List<T>)
ensures Length(xs) == Length'(xs)
{
    match xs
    case Nil =>
    case Cons(_,tail) => calc
    {
        Length(xs);
        == 
        Length'(xs);
    }
}

function Snoc<T>(xs: List<T>, y: T): List<T> {
  match xs
  case Nil => Cons(y, Nil)
  case Cons(x, tail) => Cons(x, Snoc(tail, y))
}

lemma {:induction false} LengthSnoc<T>(xs: List<T>, x: T)
  ensures Length(Snoc(xs, x)) == Length(xs) + 1
{
    match xs
    case Nil =>
    case Cons(_, tail) =>
    calc
    {
        Length(Snoc(xs, x)); 
        == // def. Snoc
        Length(Cons(x, Snoc(tail, x)));
        == // def. Length
        1 + Length(Snoc(tail, x));
        == { LengthSnoc(tail, x); } // This recursive call is accepted because tail is a substructure of xs.
        Length(xs) + 1;
    }
}