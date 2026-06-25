import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCumulativeFormationCongruence

/-! # FX1PolyAudit/.../HasTypeUnionCumulativeFormationCongruence — zero-axiom gate for the cumulative arm

Per-declaration zero-axiom gate for the cumulative (Π/Σ/List/Option) formation obligation transform: the two
binder helpers (the domain step uses native context conversion) + the spine-dispatching master.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.cumulativeBinderObligationsHoldAfterDomainStep
#assert_no_axioms FX1Poly.Typed.cumulativeBinderObligationsHoldAfterCodomainStep
#assert_no_axioms FX1Poly.Typed.cumulativeFormationPremisesHoldAfter

end FX1PolyAudit
