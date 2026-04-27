// Pattern match on Nat scrutinee.  Exercises: match on inductive,
// Zero / Succ(p) pattern binding, indRec eliminator compile.
fn pred(n: Nat) : Nat = match n;
  Zero    => Nat.Zero;
  Succ(p) => p;
end match;
