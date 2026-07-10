import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutMultiGapFactorization

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutMultiGapFactorization — zero-axiom gate for the
arbitrary-arity forward splice (fixed wire count) + the decider-fed assembly

Per-declaration zero-axiom gate for the fixed-boundary gap-fill, the source / canonical folds, the arbitrary-arity
splice, the B1 non-vacuity, the r4 two-sided decision extraction + assembly (B2), and the honesty markers.

Note: NO bespoke-free `#assert_constant_free_of` gate is claimed here.  The decider-fed witnesses route through the
r4 two-sided decision (whose bespoke-free scope is asserted, unchanged, on `pushoutRightImageTwoSidedDecision`), but
the r5 assembly witnesses are NEW constants and are NOT claimed bespoke-free (per the wire-changing wall; see the
source file docstring).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.endoGapFoldSource
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallGapCanonicalForm
#assert_no_axioms FX1Poly.Polygraph.Amalgam.multiGapEndoSplice
#assert_no_axioms FX1Poly.Polygraph.Amalgam.multiGapForwardFills
#assert_no_axioms FX1Poly.Polygraph.Amalgam.multiGapForwardSpliceWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.decidedLeftUnitRightImageConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.decidedMultiGapFills
#assert_no_axioms FX1Poly.Polygraph.Amalgam.decidedMultiGapSpliceWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasMultiGapEndoSpliceGeneral
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_arbitraryCellFactorizationStaysWalled

end FX1PolyAudit
