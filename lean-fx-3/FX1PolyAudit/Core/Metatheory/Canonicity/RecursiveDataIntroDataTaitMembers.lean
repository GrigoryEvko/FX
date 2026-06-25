import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Canonicity.RecursiveDataIntroDataTaitMembers
import FX1Poly.Core.Metatheory.Canonicity.BasedReflCandidate
import FX1Poly.Core.Metatheory.Canonicity.CarrierAwareReducibleComponentMembers

/-! # FX1PolyAudit/Core/Metatheory/Canonicity/RecursiveDataIntroDataTaitMembers
    — zero-axiom gate for the recursive data-introduction arm of the fundamental theorem (FTGEN-9 deeper)

The two generic reduction-under-a-constructor decompositions (`stepStar_under_unaryCell` /
`stepStar_under_binaryCell`) plus the six recursive data-intro arms over `dataTaitCandidate`:

  * `natSuccDataTaitMember`     — recursive Nat (predecessor member)
  * `optionSomeDataTaitMember`  — structural Option (payload SN)
  * `eitherInlDataTaitMember` / `eitherInrDataTaitMember` — structural Either (payload SN)
  * `pairDataTaitMember`        — structural Σ (both components SN)
  * `listConsDataTaitMember`    — recursive List (head SN, tail member)

Together with the based-refl identity candidate (`reflDataTaitMember*`, the term-indexed reducibility
table, and the endpoint-conversion forward closure) and the general carrier-aware data-intro members
(`memberOfReducibleComponents` / `memberOfReducibleInl` / `memberOfReducibleInr`).  The open-scope Nat /
List structural candidates live in the sibling `StructuredCandidates` shard.  Must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.stepStar_under_unaryCell
#assert_no_axioms FX1Poly.Core.stepStar_under_binaryCell
#assert_no_axioms FX1Poly.Core.natSuccDataTaitMember
#assert_no_axioms FX1Poly.Core.optionSomeDataTaitMember
#assert_no_axioms FX1Poly.Core.eitherInlDataTaitMember
#assert_no_axioms FX1Poly.Core.eitherInrDataTaitMember
#assert_no_axioms FX1Poly.Core.pairDataTaitMember
#assert_no_axioms FX1Poly.Core.listConsDataTaitMember
#assert_no_axioms FX1Poly.Core.reflDataTaitMember
-- DEP-ID genuine path-induction (brick A): the BASED endpoint-aware identity candidate member, threading the
-- reflected point's conversion to the endpoint via the unconditional `Conv.trans`.
#assert_no_axioms FX1Poly.Core.isReflValue_ofIsReflValueAt
#assert_no_axioms FX1Poly.Core.reflDataTaitMemberAt
-- The two-endpoint based candidate the genuine idJ reducibility arm pins a general identity code to.
#assert_no_axioms FX1Poly.Core.isReflValue_ofIsReflValueBetween
#assert_no_axioms FX1Poly.Core.reflDataTaitMemberBetween
-- DEP-ID the term-indexed reducibility TABLE (reducibility twin of FTGEN-7): the family-generic classifier +
-- per-code value-predicate dispatch the `dataTermIndexed` arm consumes — Id live, bridge/gel reserved rows.
#assert_no_axioms FX1Poly.Core.Generator.isTermIndexedCode
#assert_no_axioms FX1Poly.Core.termIndexedCodeValuePredicate
#assert_no_axioms FX1Poly.Core.termIndexedCodeValuePredicate_idCode
-- DEP-ID forward-closure infrastructure: the based identity candidate is conversion-invariant in its
-- endpoints (so the dataTermIndexed reducibility arm re-fires under endpoint reduction with the same candidate
-- via ofPointwiseIff) — the two-endpoint Conv-invariance composed onto the existing `dataTaitCandidate_congr`.
#assert_no_axioms FX1Poly.Core.isReflValueBetween_convInvariant
#assert_no_axioms FX1Poly.Core.basedIdCandidate_stepStarInvariant

-- The general carrier-aware data-intro members (SN-component generalization of the `memberOfNormal*` family):
-- a constructor of REDUCIBLE carrier components is a carrier-aware member of its content-bearing candidate.
-- CR2-iterated-to-StepStar (`closedUnderStepStar`) carries component membership from the constructor to its
-- normal-form components. The data-intro the bounded carrier-aware (product/either) FT intro rows consume.
#assert_no_axioms FX1Poly.Core.closedUnderStepStar
#assert_no_axioms FX1Poly.Core.carrierAwarePairCandidate.memberOfReducibleComponents
#assert_no_axioms FX1Poly.Core.carrierAwareEitherCandidate.memberOfReducibleInl
#assert_no_axioms FX1Poly.Core.carrierAwareEitherCandidate.memberOfReducibleInr

end FX1PolyAudit
