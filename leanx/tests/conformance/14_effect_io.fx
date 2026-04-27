// `with IO` on signature.  Exercises: B3 surface effect row
// parsing, A12 effect subsumption (body carries no IO call
// itself, so IO-declared is an over-declare which A12
// still admits — Tot ≤ IO by lattice).
fn log_placeholder(n: Nat) : Nat with IO = Nat.Succ(n);
