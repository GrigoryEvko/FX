import FX1Poly.Typed.FundamentalAtAllPositiveArguments

/-! # FX1Poly/Typed/ReducibleMemberAtAllPositiveLevelsStronglyNormalizing
    — CR1 for the all-positive member family: members strongly normalize

The strong-normalization (CR1) extraction for `IsReducibleMemberAtAllPositiveLevels`.  The family's shape /
transport arms (`ofNeutralClassifier` / `piTypeMemberExtension` / `extensionHeadExpand` / `castAlongConv`)
all PRODUCE all-positive membership; this is the canonical fact every all-positive member CONSUMES into —
strong normalization of the term.  It is the member-extension counterpart of the single-level
`IsReducibleMemberAt.stronglyNormalizing`, read at the bottom positive fuel via `atLevel 0`.

This is the bridge the strong-normalization-for-well-typed corollary depends on: once a binder/telescope arm
strengthens a one-level member to all-positive membership, CR1 turns it back into the SN fact canonicity and
consistency consume.  (At scope `0` the closed corollary routes through a renaming reflection — see the
`HasTypeDescPi.closedSubject…StronglyNormalizing…` family; this lemma is the non-empty-scope CR1 projection
those closed corollaries build on.)

## Zero-axiom verification

`atLevel 0` projects the all-positive family to membership at fuel `1`; the single-level CR1
`IsReducibleMemberAt.stronglyNormalizing` (positive-fuel arrow/universe candidates have genuine CR1) returns
strong normalization.  No induction.  Verified `#print axioms` clean: no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **CR1 for the all-positive member family.**  Every all-positive member of a classifier is strongly
normalizing — read the family at the bottom positive fuel (`atLevel 0`) and apply the single-level CR1.  The
member-extension counterpart of `IsReducibleMemberAt.stronglyNormalizing`; the SN bridge consumed by the
strong-normalization / canonicity corollaries. -/
theorem IsReducibleMemberAtAllPositiveLevels.stronglyNormalizing {scope : Nat}
    {typeCode term : RawTerm (scope + 1)}
    (member : IsReducibleMemberAtAllPositiveLevels typeCode term) :
    IsStronglyNormalizing term :=
  (member.atLevel 0).stronglyNormalizing

end FX1Poly.Typed
