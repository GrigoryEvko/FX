// Q77: let-bound parameterized-inductive values can be matched.
//
// Follow-up to Q76 (fn-param scrutinees).  Q76 landed Scope
// type hints via `pushWithType` at fn-parameter binder sites.
// Q77 extends that to let bindings — both the block-form
// `letStmt` in `elabStmtChain` and the expression-form
// `letBind` in `elabExpr`.  Let-bound names with an explicit
// type annotation now carry that type in the Scope, so
// `match m` on `m: Option(T)` works whether `m` comes from a
// fn param (Q76) or a let binding (Q77).
//
// Still deferred: let bindings without a type annotation (a
// synthesis probe could recover the type from the RHS, but the
// code would duplicate `inferLetRhsType?`'s logic — a small
// follow-up), lambda params without annotation, and match-arm
// ctor-arg bindings (which need `substParams` on the ctor arg
// types before registering).

// Block-form let with matching.
fn let_block_some() : Nat
begin fn
  let m : Option(Nat) = Option.Some(Nat.Succ(Nat.Succ(Nat.Zero)));
  let n : Nat = match m;
    None    => Nat.Zero;
    Some(x) => x;
  end match;
  return n;
end fn;

fn let_block_none() : Nat
begin fn
  let m : Option(Nat) = Option.None;
  let n : Nat = match m;
    None    => Nat.Zero;
    Some(x) => x + x;
  end match;
  return n;
end fn;

// Let-binding of a nested Option.
fn let_nested_inner() : Nat
begin fn
  let outer : Option(Option(Nat)) =
    Option.Some(Option.Some(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))));
  let unwrapped_outer : Option(Nat) = match outer;
    None          => Option.None;
    Some(inner)   => inner;
  end match;
  let final_n : Nat = match unwrapped_outer;
    None    => Nat.Zero;
    Some(x) => x;
  end match;
  return final_n;
end fn;

fn let_nested_outer_none() : Nat
begin fn
  let outer : Option(Option(Nat)) = Option.None;
  let unwrapped_outer : Option(Nat) = match outer;
    None        => Option.None;
    Some(inner) => inner;
  end match;
  let final_n : Nat = match unwrapped_outer;
    None    => Nat.Zero;
    Some(x) => x;
  end match;
  return final_n;
end fn;

// Option over Bool via let.
fn let_bool_some_true() : Bool
begin fn
  let m : Option(Bool) = Option.Some(Bool.True);
  let b : Bool = match m;
    None    => Bool.False;
    Some(x) => x;
  end match;
  return b;
end fn;

fn main() : Nat = let_block_some();
