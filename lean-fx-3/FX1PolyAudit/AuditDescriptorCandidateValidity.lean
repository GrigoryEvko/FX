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
-- FTGEN-2: the generator-keyed premise-free candidate dispatch + validity + coverage/boundary pins.
#assert_no_axioms FX1Poly.Typed.closedCandidateOfGenerator
#assert_no_axioms FX1Poly.Typed.closedCandidateOfGenerator_valid
#assert_no_axioms FX1Poly.Typed.closedCandidateOfGenerator_natCode
#assert_no_axioms FX1Poly.Typed.closedCandidateOfGenerator_boolCode
#assert_no_axioms FX1Poly.Typed.closedCandidateOfGenerator_eitherCode
#assert_no_axioms FX1Poly.Typed.closedCandidateOfGenerator_sigmaTyCode
#assert_no_axioms FX1Poly.Typed.closedCandidateOfGenerator_idCode
#assert_no_axioms FX1Poly.Typed.closedCandidateOfGenerator_gelCode
#assert_no_axioms FX1Poly.Typed.closedCandidateOfGenerator_sprop
#assert_no_axioms FX1Poly.Typed.closedCandidateOfGenerator_piTyCode_none
#assert_no_axioms FX1Poly.Typed.closedCandidateOfGenerator_equivCode_none
#assert_no_axioms FX1Poly.Typed.closedCandidateOfGenerator_lam_none

end FX1PolyAudit
