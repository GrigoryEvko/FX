// Q55: prelude Nat is `isCopy := true`, so a fn parameter of
// type Nat has usage = ω (§6.3 dim 3) and admits multi-use at
// every binding site without a surface `ref` annotation.
//
// Pre-Q55 this file would fire M001 at `times.Succ(p)` — the
// classical Peano product.  After Q55 the multiplication is
// linguistically clean:
//
//   fn times(a: Nat, b: Nat) : Nat = ...
//
// The same applies to plus's `b` in the Zero arm versus the
// Succ arm join (Q53's join check picked this up trivially,
// but the recursive call's extra reference now joins to ω
// and rides on Nat's isCopy propagation).
//
// Conformance gate: `fxi run` returns factorial-style
// composition without any grade-annotation gymnastics.
fn plus(a: Nat, b: Nat) : Nat = match a;
  Zero    => b;
  Succ(p) => Nat.Succ(plus(a: p, b: b));
end match;

fn times(a: Nat, b: Nat) : Nat = match a;
  Zero    => Nat.Zero;
  Succ(p) => plus(a: b, b: times(a: p, b: b));
end match;

fn main() : Nat =
  times(a: Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero))),
        b: Nat.Succ(Nat.Succ(Nat.Zero)));
