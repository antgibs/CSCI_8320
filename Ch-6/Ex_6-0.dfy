datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat {
  match xs
  case Nil => 0
  case Cons(_, tail) => 1 + Length(tail)
}

function Length'<T>(xs: List<T>): nat {
  if xs == Nil then 0 else 1 + Length'(xs.tail)
}

lemma {:induction false} LengthIsLength'<T>(xs: List<T>)
ensures Length(xs) == Length'(xs)
{
    match xs
    case Nil =>
    case Cons(x,tail) => calc
    {
        Length(xs);
        == 
        Length(Cons(x, tail));
        == // def. Length
        1 + Length(tail);
        == { LengthIsLength'(tail); }
        1 + Length'(tail);
        ==
        Length'(Cons(x, tail));
        ==
        Length'(xs);
    }
}