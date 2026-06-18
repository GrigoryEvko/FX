import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Rewrite.ModularSNBoundary

/-! # FX1PolyAudit/AuditTier0TermModularSNBoundary — zero-axiom gate for term-19 (exact SN boundary)

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Term/Rewrite/ModularSNBoundary.lean`: the persistence
direction (`strongNorm_subrelation` / `strongNorm_union_left` / `strongNorm_union_right`) and the necessity
counterexample (`forwardStep` / `backwardStep` / `unionStep` each strongly normalizing or not —
`forwardStep_isStronglyNormalizing` / `backwardStep_isStronglyNormalizing` /
`unionStep_notStronglyNormalizing`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Persistence: SN restricts to subsystems + the union-to-components projection
#assert_no_axioms FX1Poly.Core.strongNorm_subrelation
#assert_no_axioms FX1Poly.Core.strongNorm_union_left
#assert_no_axioms FX1Poly.Core.strongNorm_union_right

-- The necessity counterexample: two SN relations whose union loops
#assert_no_axioms FX1Poly.Core.forwardStep
#assert_no_axioms FX1Poly.Core.backwardStep
#assert_no_axioms FX1Poly.Core.unionStep
#assert_no_axioms FX1Poly.Core.forwardStep_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.backwardStep_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.unionStep_notStronglyNormalizing

-- The sharpened necessity: no normal form (not even WN) + the explicit infinite reduction sequence
#assert_no_axioms FX1Poly.Core.unionStep_negation
#assert_no_axioms FX1Poly.Core.unionStep_hasNoNormalForm
#assert_no_axioms FX1Poly.Core.unionCycle
#assert_no_axioms FX1Poly.Core.unionCycle_steps

end FX1PolyAudit
