import FX1Poly.Typed.HasTypeDescSound
import FX1Poly.Typed.HasTypeDescValidity
import FX1Poly.Typed.HasTypeStronglyNormalizing

/-! # FX1Poly/Typed/HasTypeDescStronglyNormalizing
    — strong normalization and typed conversion for the description formation engine

The description formation engine `HasTypeDesc` is equivalent to the native pi/sigma-formation
`HasType` core (`HasType.toHasTypeDesc` / `HasTypeDesc.toHasType`).  This file records the
normalization and typed-conversion consequences on the `HasTypeDesc` side explicitly, without claiming
anything about the grown `HasTypeDescPi` engine with lambda/application.

These theorems are intentionally scoped to the description formation engine: their proofs route through the
already-gated soundness map into native `HasType`, whose subjects are non-stepping and therefore strongly
normalizing.  The reducibility-based theorem for `HasTypeDescPi` remains the separate open assembly.

## Zero-axiom verification

Each proof is a direct composition of already-gated zero-axiom declarations:
`HasTypeDesc.toHasType`, `HasType.isStronglyNormalizing`, `IsType.isStronglyNormalizing`, and
`Conv.trans_of_typedMiddle`.  No recursion, no proof search, and no use of `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Strong normalization for the description formation engine.  A `HasTypeDesc` derivation maps to the
native pi/sigma-formation `HasType` core by soundness, and native typed subjects are strongly normalizing
because that core has no redex-creating subject constructors. -/
theorem HasTypeDesc.isStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject :=
  (HasTypeDesc.toHasType typed).isStronglyNormalizing

/-- Convert an intrinsic description-engine type witness into the corresponding native `IsType` witness.
This is the type-level form of `HasTypeDesc.toHasType`. -/
theorem IsTypeDesc.toIsType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isTypeDesc : IsTypeDesc profile context classifier) :
    IsType profile context classifier := by
  obtain ⟨levelExpr, flag, typed⟩ := isTypeDesc
  exact ⟨levelExpr, flag, HasTypeDesc.toHasType typed⟩

/-- A description-engine type is strongly normalizing. -/
theorem IsTypeDesc.isStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isTypeDesc : IsTypeDesc profile context classifier) :
    StepStar.IsStronglyNormalizing classifier :=
  isTypeDesc.toIsType.isStronglyNormalizing

/-- The classifier of a description-engine typing derivation is strongly normalizing in every
well-formed context.  This is the classifier-side companion to `HasTypeDesc.isStronglyNormalizing`:
intrinsic validity first turns the classifier into an `IsTypeDesc`, and the type-level SN projection then
normalizes it. -/
theorem HasTypeDesc.classifierStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContext context)
    (typed : HasTypeDesc profile context subject classifier) :
    StepStar.IsStronglyNormalizing classifier :=
  (typed.classifierIsTypeDesc wellFormed).isStronglyNormalizing

/-- Formation-engine subject and classifier strong normalization, packaged in the shape consumed by the
first metatheory spine.  This is deliberately scoped to `HasTypeDesc`: it routes through the proven
formation-engine equivalence with `HasType`, not through the open dependent reducibility theorem for
`HasTypeDescPi`. -/
theorem HasTypeDesc.subjectAndClassifierStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContext context)
    (typed : HasTypeDesc profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject ∧ StepStar.IsStronglyNormalizing classifier :=
  ⟨typed.isStronglyNormalizing, typed.classifierStronglyNormalizing wellFormed⟩

/-- Closed formation-engine subject and classifier strong normalization.  The empty context is
well-formed, so the general subject/classifier package specializes without any environmental premise. -/
theorem HasTypeDesc.closedSubjectAndClassifierStronglyNormalizing {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile TypingContext.empty subject classifier) :
    StepStar.IsStronglyNormalizing subject ∧ StepStar.IsStronglyNormalizing classifier :=
  typed.subjectAndClassifierStronglyNormalizing
    (WfContext.emptyIsWellFormed (profile := profile))

/-- Typed conversion transitivity through a description-engine middle type.  This is the
`HasTypeDesc`-side wrapper around the native typed-middle Newman bridge. -/
theorem Conv.trans_of_hasTypeDescMiddle {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {firstType middleType lastType : RawTerm scope}
    (middleIsTypeDesc : IsTypeDesc profile context middleType)
    (firstConv : Conv firstType middleType)
    (middleConv : Conv middleType lastType) :
    Conv firstType lastType :=
  Conv.trans_of_typedMiddle middleIsTypeDesc.toIsType firstConv middleConv

end FX1Poly.Typed
