// Wildcard lambda as a higher-order fn argument (B11 landing).
// Exercises: the expected-type threading at call sites so a
// wildcard lambda parameter can infer its domain from the
// callee's declared Pi type.  Pre-B11 this failed with E010
// "wildcard lambda parameter requires an expected Pi-type".
//
// `apply` declares `f: Nat -> Nat`; when we pass `fn(_) =>
// Nat.Zero` as the f argument, the elaborator threads `Nat ->
// Nat` as the lambda's expected type, so the wildcard's domain
// resolves to `Nat`.
fn apply(f: Nat -> Nat, x: Nat) : Nat = f(x);

fn main() : Nat = apply(f: fn(_) => Nat.Zero, x: Nat.Succ(Nat.Zero));
