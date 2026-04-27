// Use a polymorphic fn with an explicit named type argument.
// Exercises: cross-decl refs, named type-arg at call site (`a:
// Nat`), poly instantiation to concrete Nat.
fn identity<a: type>(x: a) : a = x;

fn use_identity(n: Nat) : Nat = identity(a: Nat, x: n);
