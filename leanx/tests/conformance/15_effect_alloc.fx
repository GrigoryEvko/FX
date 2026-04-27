// `with Alloc` effect row.  Distinct from IO — separate Effect
// record field.  Exercises: single-label effect parsing, A12
// subsumption on Alloc bit alone.
fn alloc_placeholder(n: Nat) : Nat with Alloc = Nat.Succ(n);
