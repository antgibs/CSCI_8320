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
function Append<T>(xs: List<T>, ys: List<T>): List<T>
  ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
{
  match xs
  case Nil => ys
  case Cons(x, tail) => Cons(x, Append(tail, ys))
}

lemma {:induction false} SnocIsAppend<T>(xs: List<T>, y: T)
ensures Snoc(xs, y) == Append(xs, Cons(y, Nil))
{
    match xs
    case Nil =>
    case Cons(x, tail) =>
    calc 
    {
        Snoc(xs, y);
        == //def. Snoc
        Cons(x, Snoc(tail, y));
        == { SnocIsAppend(tail, y); }
        Cons(x, Append(tail, Cons(y, Nil)));
        == // def. Append 
        Append(xs, Cons(y, Nil));
    }
}

// Exercise 6.4 below
lemma {:induction false} AppendAssociative<T>(xs: List<T>, ys: List<T>, zs: List<T>)
  ensures Append(Append(xs, ys), zs) == Append(xs, Append(ys, zs))
{
  match xs
  case Nil =>
  case Cons(x, tail) => calc
    {
      Append(Append(xs, ys), zs); 
      == // def. Append (inner)
      Append(Cons(x, Append(tail, ys)), zs);
      == // def. Append (outer)
      Cons(x, Append(Append(tail, ys), zs));
      == { AppendAssociative(tail, ys, zs); } // Shift the inner append parens to the right.
      Cons(x, Append(tail, Append(ys, zs)));
      == // def. Append (outer)
      Append(xs, Append(ys, zs));
    }
}