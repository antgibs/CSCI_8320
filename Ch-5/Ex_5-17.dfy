datatype List<T> = Nil | Cons(head: T, tail: List<T>)
datatype Op = Add | Mul
datatype Expr = Const(nat)
              | Var(string)
              | Node(op: Op, args: List<Expr>)

function Eval(e: Expr, env: map<string, nat>): nat {
  match e
  case Const(c) => c
  case Var(s) => if s in env.Keys then env[s] else 0
  case Node(op, args) => EvalList(args, op, env)
}

function EvalList(args: List<Expr>, op: Op,
                  env: map<string, nat>): nat
{
  match args
  case Nil =>
    (match op case Add => 0 case Mul => 1)
  case Cons(e, tail) =>
    var v0, v1 := Eval(e, env), EvalList(tail, op, env);
    match op
    case Add => v0 + v1
    case Mul => v0 * v1
}

function Substitute(e: Expr, n: string, c: nat): Expr
{
  match e
  case Const(_) => e
  case Var(s) => if s == n then Const(c) else e
  case Node(op, args) => Node(op, SubstituteList(args, n, c))
}

function SubstituteList(es: List<Expr>, n: string, c: nat): List<Expr>
{
  match es
  case Nil => Nil
  case Cons(e, tail) =>
    Cons(Substitute(e, n, c), SubstituteList(tail, n, c))
}

lemma EvalSubstitute(e: Expr, n: string, c: nat, env: map<string, nat>)
  ensures Eval(Substitute(e, n, c), env) == Eval(e, env[n := c])
{
  match e
  case Const(_) =>
  case Var(_) =>
  case Node(op, args) =>
    EvalSubstituteList(args, op, n, c, env);
}

lemma {:induction false} EvalSubstituteList(
    args: List<Expr>, op: Op, n: string, c: nat, env: map<string, nat>)
  ensures EvalList(SubstituteList(args, n, c), op, env)
       == EvalList(args, op, env[n := c])
{
  match args
  case Nil =>
  case Cons(e, tail) =>
    EvalSubstitute(e, n, c, env);
    EvalSubstituteList(tail, op, n, c, env);
}

// Lemma to prove
lemma EvalEnvDefault(e: Expr, n: string, env: map<string,nat>)
    requires n !in env.Keys
    ensures Eval(e, env) == Eval(Substitute(e, n, 0), env)
{
    match e
    case Const(_) =>
    case Var(_) =>
    case Node(op, args) => calc
    {
      Eval(Substitute(e, n, 0), env);
      == // def. Substitute
      Eval(Node(op, SubstituteList(args, n, 0)), env);
      == // def. SubstituteList
      Eval(Node(op,
                match args
                case Nil => Nil
                case Cons(e, tail) =>
                  Cons(Substitute(e, n, 0), SubstituteList(tail, n, 0))), 
                env
      );
      == { EvalEnvDefault(e, n, env); } // Get rid of empty cases
      Eval(Node(op, Cons(Substitute(e, n, 0), SubstituteList(args, n, 0))), env);
      ==
      Eval(e, env);
    }
}

/* Do not worry about code below. */

function Unit(op: Op): nat {
  match op case Add => 0 case Mul => 1
}

function Optimize(e: Expr): Expr {
  if e.Node? then
    var args := OptimizeAndFilter(e.args, Unit(e.op));
    Shorten(e.op, args)
  else
    e // no change
}

function Shorten(op: Op, args: List<Expr>): Expr {
  match args
  case Nil => Const(Unit(op))
  case Cons(e, Nil) => e
  case _ => Node(op, args)
}

function OptimizeAndFilter(es: List<Expr>, unit: nat): List<Expr>
{
  match es
  case Nil => Nil
  case Cons(e, tail) =>
    var e', tail' := Optimize(e), OptimizeAndFilter(tail, unit);
    if e' == Const(unit) then tail' else Cons(e', tail')
}

lemma OptimizeCorrect(e: Expr, env: map<string, nat>)
  ensures Eval(Optimize(e), env) == Eval(e, env) 
{
  if e.Node? {
    var args := OptimizeAndFilter(e.args, Unit(e.op));
    calc {
      Eval(Optimize(e), env);
    ==  // def. Optimize
      Eval(Shorten(e.op, args), env);
    ==  { ShortenCorrect(e.op, args, env); }
      Eval(Node(e.op, args), env);
    ==  { OptimizeAndFilterCorrect(e.args, e.op, env); }
      Eval(Node(e.op, e.args), env);
    }
  }
}

lemma ShortenCorrect(op: Op, args: List<Expr>, env: map<string, nat>)
  ensures Eval(Shorten(op, args), env) == Eval(Node(op, args), env) 
{
  match args
  case Nil =>
  case Cons(a, Nil) =>
    calc {
      Eval(Node(op, Cons(a, Nil)), env);
    ==  // def. Eval
      EvalList(Cons(a, Nil), op, env);
    ==  // def. EvalList
      var v0, v1 := Eval(a, env), EvalList(Nil, op, env);
      match op
      case Add => v0 + v1
      case Mul => v0 * v1;
    ==  // def. EvalList
      var v0, v1 := Eval(a, env), Unit(op);
      match op
      case Add => v0 + v1
      case Mul => v0 * v1;
    ==  // substitute for v0, v1
      match op
      case Add => Eval(a, env) + Unit(op)
      case Mul => Eval(a, env) * Unit(op);
    ==  // def. Unit in each case
      Eval(a, env);
    }
  case _ =>
}

lemma OptimizeAndFilterCorrect(args: List<Expr>, op: Op,
                               env: map<string, nat>)
  ensures Eval(Node(op, OptimizeAndFilter(args, Unit(op))), env)
       == Eval(Node(op, args), env) 
{
  match args
  case Nil =>
  case Cons(e, tail) =>
    OptimizeCorrect(e, env);
    OptimizeAndFilterCorrect(tail, op, env);
}
