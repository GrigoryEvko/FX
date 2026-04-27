// Module-private const declaration.  Per §5.5, `const NAME : T
// = expr;` is always module-private and compile-time evaluated.
// Exercises: B13 top-level const elaboration, no pub permitted.
const MAX_DEPTH : Nat = Nat.Succ(Nat.Succ(Nat.Succ(Nat.Zero)));

// Use the const from a fn — resolves via Term.const lookup.
fn use_const() : Nat = MAX_DEPTH;
