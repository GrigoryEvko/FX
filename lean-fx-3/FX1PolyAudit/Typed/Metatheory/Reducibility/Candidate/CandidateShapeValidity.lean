import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Reducibility.Candidate.CandidateShapeValidity

/-! # FX1PolyAudit/AuditCandidateShapeValidity
    — zero-axiom gate for the per-shape candidate validity (FTGEN-2)

Every data-like descriptor shape's candidate is `CandidateValidity` (= the kernel Girard CR record), discharged
unconditionally via the kernel `dataTaitCandidate_isReducibilityCandidate` / `emptyTaitCandidate_is
ReducibilityCandidate` / the SN base — including the in-arc frontier formers gelCode (relationalSaturated) and
sprop (strictPropIrrelevant).  All must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.constructorHeadValue
#assert_no_axioms FX1Poly.Typed.inductiveSaturatedCandidate
#assert_no_axioms FX1Poly.Typed.inductiveSaturatedCandidate_valid
#assert_no_axioms FX1Poly.Typed.singleHeadCandidate
#assert_no_axioms FX1Poly.Typed.singleHeadCandidate_valid
#assert_no_axioms FX1Poly.Typed.dependentSumCandidate_valid
#assert_no_axioms FX1Poly.Typed.identitySaturatedCandidate_valid
#assert_no_axioms FX1Poly.Typed.relationalSaturatedCandidate_valid
#assert_no_axioms FX1Poly.Typed.emptyDataCandidate_valid
#assert_no_axioms FX1Poly.Typed.strictPropIrrelevantCandidate_valid

end FX1PolyAudit
