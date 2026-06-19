import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Reducibility.Candidate.ReducibilityCandidateDesc

/-! # FX1PolyAudit/AuditReducibilityCandidateDesc
    — zero-axiom gate for the universal reducibility-candidate signature (FTGEN-1 data layer)

Per-declaration zero-axiom gate for
`FX1Poly/Typed/Metatheory/Reducibility/Candidate/ReducibilityCandidateDesc.lean`: the generator-agnostic
candidate combinator algebra + the 208-generator dispatch `candidateDescOf` (composed propext-cleanly via
`DecidableEq Generator` `if`-chains, NO wildcard match) + the per-former coverage / exclusion theorems +
the live roster. All must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.candidateDescOf
#assert_no_axioms FX1Poly.Typed.boolCandidateSpecs
#assert_no_axioms FX1Poly.Typed.natCandidateSpecs
#assert_no_axioms FX1Poly.Typed.listCandidateSpecs
#assert_no_axioms FX1Poly.Typed.optionCandidateSpecs
#assert_no_axioms FX1Poly.Typed.coproductCandidateSpecs
#assert_no_axioms FX1Poly.Typed.unitCandidateSpecs
#assert_no_axioms FX1Poly.Typed.intervalCandidateSpecs
#assert_no_axioms FX1Poly.Typed.candidateDescOf_piTyCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_arrowCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_sigmaTyCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_productCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_boolCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_natCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_listCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_optionCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_eitherCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_sumCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_unitCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_emptyCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_intervalCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_idCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_bridgeCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_equivCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_universeCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_gelCode
#assert_no_axioms FX1Poly.Typed.candidateDescOf_sprop
#assert_no_axioms FX1Poly.Typed.candidateDescOf_lam_none
#assert_no_axioms FX1Poly.Typed.candidateDescOf_app_none
#assert_no_axioms FX1Poly.Typed.candidateDescOf_ungel_none
#assert_no_axioms FX1Poly.Typed.liveCandidateFormers_length

end FX1PolyAudit
