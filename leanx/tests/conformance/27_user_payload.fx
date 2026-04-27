// User-defined ADT with payload arg (B9 ADT translation).
// Exercises: ctor with positional payload at decl site,
// ctor application at runtime with Nat-typed arg, match arm
// binding the payload via pattern variable `n`.
type natbox
  Empty;
  One(Nat);
end type;

fn peek(b: natbox) : Nat = match b;
  Empty  => Nat.Zero;
  One(n) => n;
end match;

fn main() : Nat = peek(One(Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)))));
