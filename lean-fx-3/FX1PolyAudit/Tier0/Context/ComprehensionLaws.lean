import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ComprehensionLaws

/-! # FX1PolyAudit/AuditTier0ContextLaws — zero-axiom gate for context-1's earned CwF laws

Per-declaration zero-axiom gate for the earned CwF comprehension theory
(`FX1Poly/Tier0/Context/ComprehensionLaws.lean`): inclusion faithfulness (via the
`RawTerm` constructor's `injection`), the comprehension η-law, the lift functor +
display-map naturality, the comprehension representability bijection, and the
inclusion's display-preservation.  Every declaration below must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Faithfulness — earning the `⊂`
#assert_no_axioms FX1Poly.Tier0.RenamingVec.toSubstVec_injective
#assert_no_axioms FX1Poly.Tier0.renamingInclusion_faithful

-- Comprehension η / surjective pairing
#assert_no_axioms FX1Poly.Tier0.SubstVec.identity_succ_eq_cons

-- The lift functor + display-map naturality
#assert_no_axioms FX1Poly.Tier0.SubstVec.lift
#assert_no_axioms FX1Poly.Tier0.SubstVec.weakening_compose_lift

-- Comprehension as a genuine bijection
#assert_no_axioms FX1Poly.Tier0.SubstVec.comprehensionBackward_forward
#assert_no_axioms FX1Poly.Tier0.SubstVec.comprehensionForward_backward
#assert_no_axioms FX1Poly.Tier0.SubstVec.comprehensionIso

-- The inclusion preserves the display structure
#assert_no_axioms FX1Poly.Tier0.RenamingVec.weakening_toSubstVec

end FX1PolyAudit
