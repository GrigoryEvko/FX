// Self-recursive via Term.const knot.  Phase-2 elaborator resolves
// the bare `double(p)` reference to `Term.const "double"` through
// the two-pass checkFile — no `rec` keyword needed at the surface.
// Exercises: self-reference via two-pass GlobalEnv, iota iotaArgs
// self-reference detection on the Succ payload.
fn double(n: Nat) : Nat = match n;
  Zero    => Nat.Zero;
  Succ(p) => Nat.Succ(Nat.Succ(double(p)));
end match;
