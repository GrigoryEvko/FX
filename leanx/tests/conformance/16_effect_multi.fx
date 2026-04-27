// Multiple effects on the same signature.  Exercises: comma-
// separated `with` row, Effect record with three bits set, A12
// subsumption across the product.
fn multi_effect(n: Nat) : Nat with IO, Alloc, Async = Nat.Succ(n);
