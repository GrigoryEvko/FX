// Nested match — match inside a match arm.  Exercises: scope
// threading through the outer pattern's binders, Ind-elim under
// Ind-elim, iota reduction in a context with a bound ctor arg.
fn depth_two(outer: Nat) : Nat = match outer;
  Zero => Nat.Zero;
  Succ(p) =>
    match p;
      Zero     => Nat.Succ(Nat.Zero);
      Succ(pp) => Nat.Succ(Nat.Succ(pp));
    end match;
end match;
