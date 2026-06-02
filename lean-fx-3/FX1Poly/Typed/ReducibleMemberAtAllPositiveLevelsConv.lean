import FX1Poly.Typed.FundamentalAtAllPositiveArguments

/-! # FX1Poly/Typed/ReducibleMemberAtAllPositiveLevelsConv
    — member-extension transports across type CONVERSION

The conversion arm of the member-extension family.  Where `ofNeutralClassifier` / `piTypeMemberExtension` /
`extensionHeadExpand` discharge member-extension by the SHAPE of the classifier, this file transports it
across the kernel conversion relation: if `term` is a member of `typeLeft` at all positive levels, `typeLeft`
is convertible to `typeRight`, and `typeRight` is itself reducible at all positive levels, then `term` is a
member of `typeRight` at all positive levels.

Per level the single-level `IsReducibleMemberAt.castAlongConv` (built on `ReducibleTypeAt.convTransfer`) ports
the membership to the target candidate; the all-positive wrapper just supplies, at each positive level, the
target candidate that `IsReducibleTypeAtAllPositiveLevels typeRight` provides.

This is the general conversion-transport for member-extension — strictly more flexible than the single-step
`extensionHeadExpand` (which only crosses ONE weak-head step and reconstructs the redex's reducibility from
the step): it crosses an ARBITRARY `Conv` provided the target's all-positive reducibility is supplied
independently.  It is the conv arm of the strengthened formation-FT motive (carry member-extension as a
conclusion): a type-code subject whose denoted type is presented up to conversion discharges member-extension
on a convertible representative and transports back.

## Zero-axiom verification

`intro` the positive level, project the target candidate from `IsReducibleTypeAtAllPositiveLevels`, apply the
single-level `castAlongConv`; no induction.  Verified `#print axioms` clean: no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Member-extension transports across type conversion.**  All-positive membership in `typeLeft` carries to
all-positive membership in any convertible `typeRight` that is itself reducible at all positive levels.  The
all-positive wrapper of `IsReducibleMemberAt.castAlongConv`; the conv arm of the member-extension family,
complementing the shape arms (`ofNeutralClassifier` / `piTypeMemberExtension` / `extensionHeadExpand`). -/
theorem IsReducibleMemberAtAllPositiveLevels.castAlongConv {scope : Nat}
    {typeLeft typeRight term : RawTerm scope}
    (member : IsReducibleMemberAtAllPositiveLevels typeLeft term)
    (targetAllPositive : IsReducibleTypeAtAllPositiveLevels typeRight)
    (conv : Conv typeLeft typeRight) :
    IsReducibleMemberAtAllPositiveLevels typeRight term := by
  intro posLevel
  obtain ⟨candidateRight, targetReducible⟩ := targetAllPositive posLevel
  exact IsReducibleMemberAt.castAlongConv (member posLevel) targetReducible conv

/-- **Member-extension transports across conversion, target reducible at ALL levels.**  Convenience form of
`IsReducibleMemberAtAllPositiveLevels.castAlongConv` taking the strictly stronger `IsReducibleTypeAtAllLevels`
target hypothesis (the shape the type-level-irrelevance lemmas produce); downcasts to all-positive levels. -/
theorem IsReducibleMemberAtAllPositiveLevels.castAlongConvOfAllLevels {scope : Nat}
    {typeLeft typeRight term : RawTerm scope}
    (member : IsReducibleMemberAtAllPositiveLevels typeLeft term)
    (targetAllLevels : IsReducibleTypeAtAllLevels typeRight)
    (conv : Conv typeLeft typeRight) :
    IsReducibleMemberAtAllPositiveLevels typeRight term :=
  member.castAlongConv (fun predLevel => targetAllLevels (predLevel + 1)) conv

end FX1Poly.Typed
