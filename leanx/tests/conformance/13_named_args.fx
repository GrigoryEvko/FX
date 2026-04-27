// Multi-parameter fn with named args.  Per §4.1 rule 6, functions
// with more than one parameter REQUIRE named args at the call
// site.  Exercises: B12's reorderNamedCallArgs, named-arg routing.
fn combine(first: Nat, second: Nat) : Nat = Nat.Succ(first);

fn caller() : Nat = combine(first: Nat.Zero, second: Nat.Succ(Nat.Zero));

// Swapped name order — same function, names route to declared
// slots regardless of source position.  Catches regressions
// where B12's reordering collapses.
fn caller_swapped() : Nat = combine(second: Nat.Succ(Nat.Zero), first: Nat.Zero);
