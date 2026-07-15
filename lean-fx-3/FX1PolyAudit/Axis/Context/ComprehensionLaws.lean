import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.ComprehensionLaws

/-! # FX1PolyAudit/AuditAxisContextLaws — zero-axiom gate for context-1's earned CwF laws

Per-declaration zero-axiom gate for the earned CwF comprehension theory
(`FX1Poly/Axis/Context/ComprehensionLaws.lean`): inclusion faithfulness (via the
`RawTerm` constructor's `injection`), the comprehension η-law, the lift functor +
display-map naturality, the comprehension representability bijection, and the
inclusion's display-preservation.  Every declaration below must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Faithfulness — earning the `⊂`
#assert_no_axioms FX1Poly.Axis.RenamingVec.toSubstVec_injective
#assert_no_axioms FX1Poly.Axis.renamingInclusion_faithful

-- Comprehension η / surjective pairing
#assert_no_axioms FX1Poly.Axis.SubstVec.identity_succ_eq_cons

-- The lift functor + display-map naturality
#assert_no_axioms FX1Poly.Axis.SubstVec.lift
#assert_no_axioms FX1Poly.Axis.SubstVec.weakening_compose_lift

-- Comprehension as a genuine bijection
#assert_no_axioms FX1Poly.Axis.SubstVec.comprehensionBackward_forward
#assert_no_axioms FX1Poly.Axis.SubstVec.comprehensionForward_backward
#assert_no_axioms FX1Poly.Axis.SubstVec.comprehensionIso

-- The inclusion preserves the display structure
#assert_no_axioms FX1Poly.Axis.RenamingVec.weakening_toSubstVec

end FX1PolyAudit
