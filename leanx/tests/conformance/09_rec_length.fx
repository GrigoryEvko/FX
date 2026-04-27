// Recursive Nat-as-fuel walk.  Stands in for list-length since
// parameterized List specs aren't yet registered in the prelude.
// Same recursive shape as stdlib `length` — walks successor
// predecessor by predecessor.  Self-ref via Term.const knot.
fn fuel_walk(n: Nat) : Nat = match n;
  Zero    => Nat.Zero;
  Succ(p) => Nat.Succ(fuel_walk(p));
end match;
