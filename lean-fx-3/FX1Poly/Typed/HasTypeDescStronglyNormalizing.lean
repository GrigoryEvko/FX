import FX1Poly.Typed.HasTypeDescValidity
import FX1Poly.Typed.WfContextDescValidity
import FX1Poly.Typed.HasTypeDescSubjectStronglyNormalizingNative
import FX1Poly.Core.RawConfluence

/-! # FX1Poly/Typed/HasTypeDescStronglyNormalizing
    — strong normalization and typed conversion for the description formation engine

The description formation engine `HasTypeDesc` records normalization and typed-conversion consequences
on its own structure, without claiming anything about the grown `HasTypeDescPi` engine with
lambda/application.

These theorems are scoped to the description formation engine and are proved NATIVELY: SN comes
from `HasTypeDesc.subjectStronglyNormalizingNative` (the formation subject is non-stepping by its own
structure), and typed-conversion transitivity from the unconditional raw `Conv.trans` (the
raw-confluence harvest).  The reducibility-based theorem for `HasTypeDescPi` is the separate open assembly.

## Zero-axiom verification

Each proof is a direct composition of already-gated zero-axiom declarations:
`HasTypeDesc.subjectStronglyNormalizingNative`, `HasTypeDesc.classifierStronglyNormalizingNative` (the native
formation-validity SN twin over `WfContextDesc`), and `Conv.trans`.  No recursion, no proof search, and no use
of `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Strong normalization for the description formation engine: every formation-typed SUBJECT is strongly
normalizing.  Delegates to `HasTypeDesc.subjectStronglyNormalizingNative`, proved directly on the formation
engine's structure. -/
theorem HasTypeDesc.isStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject :=
  typed.subjectStronglyNormalizingNative

/-- A description-engine type is strongly normalizing.  The `IsTypeDesc` witness is a
`HasTypeDesc` derivation whose SUBJECT is the classifier, so `HasTypeDesc.subjectStronglyNormalizingNative`
normalizes it directly. -/
theorem IsTypeDesc.isStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isTypeDesc : IsTypeDesc profile context classifier) :
    StepStar.IsStronglyNormalizing classifier := by
  obtain ⟨_levelExpr, _flag, classifierTyped⟩ := isTypeDesc
  exact classifierTyped.subjectStronglyNormalizingNative

/-- The classifier of a description-engine typing derivation is strongly normalizing in every
well-formed context.  This is the classifier-side companion to `HasTypeDesc.isStronglyNormalizing`:
intrinsic validity (native, over `WfContextDesc`) first turns the classifier into an `IsTypeDesc`, and the
type-level SN projection then normalizes it.  Composes `classifierIsTypeDescNative` (formation validity, from
`WfContextDescValidity`) with the local `IsTypeDesc.isStronglyNormalizing`, threading `WfContextDesc`.
(Inlined rather than delegating to the equivalent `classifierStronglyNormalizingNative`, which imports this
file for `IsTypeDesc.isStronglyNormalizing` and so cannot be imported back without a cycle.) -/
theorem HasTypeDesc.classifierStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDesc context)
    (typed : HasTypeDesc profile context subject classifier) :
    StepStar.IsStronglyNormalizing classifier :=
  (typed.classifierIsTypeDescNative wellFormed).isStronglyNormalizing

/-- Formation-engine subject and classifier strong normalization, packaged in the shape consumed by the
first metatheory spine.  This is deliberately scoped to `HasTypeDesc`: it routes through the native
formation-engine SN twins (`subjectStronglyNormalizingNative` / `classifierStronglyNormalizingNative` over
`WfContextDesc`), not through the open dependent reducibility theorem for `HasTypeDescPi`. -/
theorem HasTypeDesc.subjectAndClassifierStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDesc context)
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
    (WfContextDesc.emptyIsWellFormed (profile := profile))

/-- Typed conversion transitivity through a description-engine middle type.  Raw `Conv` is
an unconditional equivalence relation (`Conv.trans`, the raw-confluence harvest), so transitivity
needs no typed middle at all; the `IsTypeDesc` premise is vacuous (retained for API stability). -/
theorem Conv.trans_of_hasTypeDescMiddle {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {firstType middleType lastType : RawTerm scope}
    (_middleIsTypeDesc : IsTypeDesc profile context middleType)
    (firstConv : Conv firstType middleType)
    (middleConv : Conv middleType lastType) :
    Conv firstType lastType :=
  Conv.trans firstConv middleConv

end FX1Poly.Typed
