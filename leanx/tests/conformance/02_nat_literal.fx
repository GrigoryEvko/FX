// Nat constructor construction via `Nat.Zero` / `Nat.Succ(n)`.
// Exercises: fully-qualified ctor refs, Ind-intro, literal Nat
// value construction without surface-literal support.
fn zero() : Nat = Nat.Zero;
fn one() : Nat = Nat.Succ(Nat.Zero);
fn two() : Nat = Nat.Succ(Nat.Succ(Nat.Zero));
