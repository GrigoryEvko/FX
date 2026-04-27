// Forward declaration via `val`.  Per §5.5, `val` declares a
// symbol's signature without providing a body — satisfied by a
// later `fn` with matching signature, or by an external
// implementation (extern "C").  Exercises: B13 val parsing
// + two-pass elab's treatment of signature-only entries.
val later_fn : Nat -> Nat;

fn later_fn(x: Nat) : Nat = Nat.Succ(x);
