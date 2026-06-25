import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.List.ListElimValueReducibility

/-! # FX1PolyAudit.Core.Eliminators.List.ListElimValueReducibility

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.List.ListElimValueReducibility`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The value case of listElim recursor reducibility, the list analogue of the Nat recursor value-case:
-- listElim on a list-value scrutinee lands in the result candidate by IsListValue structural induction firing
-- the two iota rules (nil to nilBranch; cons to app(app(app c head)tail)(listElim tail n c)) through the
-- candidate's weak-head expansion.  Same conditional interface (weak-head-expansion + branch reducibility +
-- SN-of-redex).
#assert_no_axioms FX1Poly.Core.listElimValueReducibility

end FX1PolyAudit
