import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Nat.NatElimValueReducibility

/-! # FX1PolyAudit.Core.Eliminators.Nat.NatElimValueReducibility

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.Nat.NatElimValueReducibility`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The value case of non-dependent Nat-recursor reducibility (the computational heart): the recursor on a
-- numeral scrutinee lands in the result candidate, by IsNatValue structural induction firing the two iota rules
-- (zero to z, succ to app(app s pred)(natElim pred z s)) through the candidate's weak-head expansion.
-- Conditional on the interface (candidate weak-head-expansion + branch reducibility + SN-of-redex).
#assert_no_axioms FX1Poly.Core.natElimValueReducibility

#assert_no_axioms FX1Poly.Core.natRecValueReducibility

end FX1PolyAudit
