import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Canonicity.RecursiveDataIntroDataTaitMembers
import FX1Poly.Core.Metatheory.Canonicity.CarrierAwareReducibleComponentMembers
import FX1Poly.Core.Metatheory.Canonicity.NatStructuredCandidate

/-! # FX1PolyAudit/AuditRecursiveDataIntroDataTaitMembers
    — zero-axiom gate for the COMPLETE recursive data-introduction arm of the fundamental theorem (FTGEN-9
    deeper)

The two generic reduction-under-a-constructor decompositions (`stepStar_under_unaryCell` /
`stepStar_under_binaryCell`) plus the six recursive data-intro arms over `dataTaitCandidate`:

  * `natSuccDataTaitMember`     — recursive Nat (predecessor member)
  * `optionSomeDataTaitMember`  — structural Option (payload SN)
  * `eitherInlDataTaitMember` / `eitherInrDataTaitMember` — structural Either (payload SN)
  * `pairDataTaitMember`        — structural Σ (both components SN)
  * `listConsDataTaitMember`    — recursive List (head SN, tail member)

With the nullary / already-normal intro arm (`inductiveSaturatedIntro`) and the closed-eliminator family
these close the data-introduction side of the FT.  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.stepStar_under_unaryCell
#assert_no_axioms FX1Poly.Core.stepStar_under_binaryCell
#assert_no_axioms FX1Poly.Core.natSuccDataTaitMember
#assert_no_axioms FX1Poly.Core.optionSomeDataTaitMember
#assert_no_axioms FX1Poly.Core.eitherInlDataTaitMember
#assert_no_axioms FX1Poly.Core.eitherInrDataTaitMember
#assert_no_axioms FX1Poly.Core.pairDataTaitMember
#assert_no_axioms FX1Poly.Core.listConsDataTaitMember

-- The general carrier-aware data-intro members (SN-component generalization of the `memberOfNormal*` family):
-- a constructor of REDUCIBLE carrier components is a carrier-aware member of its content-bearing candidate.
-- CR2-iterated-to-StepStar (`closedUnderStepStar`) carries component membership from the constructor to its
-- normal-form components. The data-intro the bounded carrier-aware (product/either) FT intro rows consume.
#assert_no_axioms FX1Poly.Core.closedUnderStepStar
#assert_no_axioms FX1Poly.Core.carrierAwarePairCandidate.memberOfReducibleComponents
#assert_no_axioms FX1Poly.Core.carrierAwareEitherCandidate.memberOfReducibleInl
#assert_no_axioms FX1Poly.Core.carrierAwareEitherCandidate.memberOfReducibleInr

-- The OPEN-SCOPE nat structural candidate (NatStructuredCandidate.lean): the `IsNatStructured` value
-- predicate (`succ^k` of `zero` or a NORMAL neutral) whose `dataTaitCandidate` is closed under `natSucc` at
-- EVERY scope, unlike the scope-0-only `natSuccDataTaitMember` above (which rules the neutral disjunct out
-- with `IsNeutral.noClosed`).  The candidate the dependent `natElim` / `natRec` reducibility pins
-- `natTypeCell` to; `natStructuredClosedReducesToNumeral` confirms the widening is conservative for closed
-- canonicity (closed members are still exactly the numerals).
#assert_no_axioms FX1Poly.Core.isNatStructured_impliesStepNormalForm
#assert_no_axioms FX1Poly.Core.isNatValue_implies_isNatStructured
#assert_no_axioms FX1Poly.Core.isNatStructured_closed_isNatValue
#assert_no_axioms FX1Poly.Core.natStructuredCandidate_isReducibilityCandidate
#assert_no_axioms FX1Poly.Core.natStructuredCandidate_headExpansionClosed
#assert_no_axioms FX1Poly.Core.isNatValue_structuredMember
#assert_no_axioms FX1Poly.Core.natZeroStructuredMember
#assert_no_axioms FX1Poly.Core.natSuccStructuredMember
#assert_no_axioms FX1Poly.Core.natStructuredClosedReducesToNumeral

end FX1PolyAudit
