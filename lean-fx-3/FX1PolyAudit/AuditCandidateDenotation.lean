import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Reducibility.Candidate.CandidateDenotation

/-! # FX1PolyAudit/AuditCandidateDenotation
    — zero-axiom gate for the candidate denotation + CandidateValidity interface (FTGEN-1 proof layer)

`CandidateValidity` (the `@[reducible]` alias of the kernel Girard CR record `IsReducibilityCandidate`), the
`neutralSaturated` base denotation + its validity, the `derivedUnfold` validity transfer (the equiv⇒Σ unlock,
via `respectsPointwiseIff`), the `dependentProduct` function-space denotation + its validity (the impredicative
heart, via the kernel `isDependentArrowReducible_isReducibilityCandidate`), the `inductiveSaturated` data Tait
denotation + its validity (via the kernel `dataTaitCandidate_isReducibilityCandidate`, for every value
predicate), and the CR3-nonemptiness re-export — all must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega` (they are direct applications of the already-audited kernel CR lemmas). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.CandidateValidity
#assert_no_axioms FX1Poly.Typed.neutralSaturatedCandidate
#assert_no_axioms FX1Poly.Typed.neutralSaturatedCandidate_valid
#assert_no_axioms FX1Poly.Typed.derivedUnfoldCandidate_valid
#assert_no_axioms FX1Poly.Typed.dependentProductCandidate
#assert_no_axioms FX1Poly.Typed.dependentProductCandidate_valid
#assert_no_axioms FX1Poly.Typed.inductiveSaturatedCandidate
#assert_no_axioms FX1Poly.Typed.inductiveSaturatedCandidate_valid
#assert_no_axioms FX1Poly.Typed.CandidateValidity.containsVariable

end FX1PolyAudit
