import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Reducibility.Candidate.DescriptorCandidateValidity

/-! # FX1PolyAudit/AuditDescriptorCandidateValidity
    — zero-axiom gate for the generic candidate-validity dispatch (FTGEN-4 core)

`descriptorClosedCandidate` (the premise-free denotation) + `descriptorClosedCandidate_valid` (the ONE generic
theorem: every candidate it produces is a Girard CR) + the coverage `rfl` pins.  All must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.descriptorClosedCandidate
#assert_no_axioms FX1Poly.Typed.descriptorClosedCandidate_valid
#assert_no_axioms FX1Poly.Typed.descriptorClosedCandidate_coversNeutral
#assert_no_axioms FX1Poly.Typed.descriptorClosedCandidate_coversRelational
#assert_no_axioms FX1Poly.Typed.descriptorClosedCandidate_coversStrictProp
#assert_no_axioms FX1Poly.Typed.descriptorClosedCandidate_dependentProduct_none

end FX1PolyAudit
