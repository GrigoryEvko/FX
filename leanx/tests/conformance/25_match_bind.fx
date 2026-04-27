// Pattern match with captured payload binding.  `Succ(p)`
// binds the predecessor as `p` and uses it twice (free-var
// count = 2).  Exercises: iotaArgs' self-reference detection
// on recursive ctor args, variable use-count tracking in an
// indRec method body.
fn succ_twice(n: Nat) : Nat = match n;
  Zero    => Nat.Succ(Nat.Zero);
  Succ(p) => Nat.Succ(Nat.Succ(p));
end match;
