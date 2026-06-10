import FX1Poly.Typed.ClosedStronglyNormalizing
import FX1Poly.Typed.TypedLambdaDerivations
import FX1Poly.Typed.ClosedConvDecision
import FX1Poly.Typed.GrownTypeSafety
import FX1Poly.Typed.TypedChurchNumeralFaithful
import FX1Poly.Core.NormalizeMeta

/-! # Foundation/PolyCell/Typed/TypedNormalizer (SN-112)
    — the term-layer normalizer keyed directly on the grown typing judgment

`Core/Normalize.lean` ships the raw normalizer `RawTerm.normalize term (accessible : Acc StepSuccessor term)`
— it iterates `reduceOnce` along an accessibility witness and halts at a normal form, with
`normalize_reducesTo` (the subject reduces to the output) and `normalize_isStepNormalForm` (the output is
normal).  `Core/NormalizeMeta.lean` rounds out the metatheory (`conv_normalize`, `normalize_eq_iff_conv`).
But that normalizer is keyed on a bare `Acc` witness — the caller must supply termination by hand.

SN-043 (`HasTypeDescPi.closedStronglyNormalizing`: every closed grown-well-typed term is
`IsStronglyNormalizing = Acc StepSuccessor`) is exactly that witness.  This file composes the two into the
TERM-LAYER NORMALIZER KEYED ON THE TYPING JUDGMENT: given a grown derivation
`HasTypeDescPi profile .empty subject classifier`, the normalizer runs with no hand-supplied termination —
typing IS the termination certificate.  This is the user-facing entry point ("I have a typing derivation,
give me the computed normal form"), distinct from the existing routes:

  * `ClosedConvDecision.closedConvDecidableFromLevelIndexed` (firing 67) keys on the LEVEL-INDEXED
    fundamental conclusion, not the grown derivation;
  * `SimplyTypedTermLF.normalForm_typed` keys on the SIMPLY-TYPED fragment, not the grown engine;
  * `HasTypeDescDecidable.Conv.decidableOfHasTypeDesc` (SN-051) is the FORMATION engine's CLASSIFIER-side
    decider, not the grown subject's normalizer.

## Contents

  * `HasTypeDescPi.normalForm` — the normal form of a closed grown-well-typed subject (the normalizer with
    SN-043 discharging termination).
  * `HasTypeDescPi.normalForm_reducesTo` / `normalForm_isStepNormalForm` / `normalForm_conv` — the subject
    reduces to its normal form, the result is structurally normal, and the subject converts to it.
  * `HasTypeDescPi.conv_iff_normalForm_eq` — two closed grown-well-typed subjects convert IFF their normal
    forms coincide: the normal form is a COMPLETE conversion invariant, keyed on the two typing derivations.
  * `HasTypeDescPi.closedConvDecidable` — the grown-engine-facing decidable conversion of two closed
    well-typed SUBJECTS, keyed directly on their derivations and UNCONDITIONAL (no level-indexed hypothesis):
    the grown twin of `Conv.decidableOfHasTypeDesc`.
  * `identityApplicationNormalForm_convReduct` — non-vacuity: the normalizer takes the closed β-redex
    `(λx. x) (Type@e)` (firing 64's `piElim` derivation) to a normal form convertible to its reduct
    `Type@e`, so the normalizer does real reduction work on a genuinely-typed redex.

## Zero-axiom verification

Each declaration composes `HasTypeDescPi.closedStronglyNormalizing` (SN-043) with the shipped raw-normalizer
correctness theorems (`RawTerm.normalize_reducesTo` / `_isStepNormalForm` / `conv_normalize` /
`normalize_eq_iff_conv`) and the SN-fragment decider `Conv.decidableOfStronglyNormalizing`; the smoke chains
`Conv.sym` / `Conv.trans` with firing 67's `betaRedexConvertsToReduct`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The normal form of a closed grown-well-typed term.**  The raw normalizer `RawTerm.normalize` run on
the subject, with SN-043 (`HasTypeDescPi.closedStronglyNormalizing`) supplying the accessibility witness —
typing is the termination certificate, so no `Acc` need be passed by hand.  The term-layer normalizer keyed
on the typing judgment. -/
def HasTypeDescPi.normalForm {profile : PolyProfile} {subject classifier : RawTerm 0}
    (typing : HasTypeDescPi profile TypingContext.empty subject classifier) : RawTerm 0 :=
  RawTerm.normalize subject (HasTypeDescPi.closedStronglyNormalizing typing)

/-- The subject reaches its normal form by a reduction chain (`StepStar`). -/
theorem HasTypeDescPi.normalForm_reducesTo {profile : PolyProfile} {subject classifier : RawTerm 0}
    (typing : HasTypeDescPi profile TypingContext.empty subject classifier) :
    StepStar subject typing.normalForm :=
  RawTerm.normalize_reducesTo subject (HasTypeDescPi.closedStronglyNormalizing typing)

/-- The normal form is structurally normal — no `Step` applies to it. -/
theorem HasTypeDescPi.normalForm_isStepNormalForm {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typing : HasTypeDescPi profile TypingContext.empty subject classifier) :
    RawTerm.isStepNormalForm typing.normalForm :=
  RawTerm.normalize_isStepNormalForm subject (HasTypeDescPi.closedStronglyNormalizing typing)

/-- The subject converts to its normal form (its reduction chain lifts to `Conv`). -/
theorem HasTypeDescPi.normalForm_conv {profile : PolyProfile} {subject classifier : RawTerm 0}
    (typing : HasTypeDescPi profile TypingContext.empty subject classifier) :
    Conv subject typing.normalForm :=
  RawTerm.conv_normalize subject (HasTypeDescPi.closedStronglyNormalizing typing)

/-- **The normal form is a complete conversion invariant for the closed grown fragment.**  Two closed
grown-well-typed subjects convert IFF their normal forms coincide — keyed on the two typing derivations, with
SN-043 discharging both termination hypotheses of `RawTerm.normalize_eq_iff_conv`. -/
theorem HasTypeDescPi.conv_iff_normalForm_eq {profile : PolyProfile}
    {subjectLeft classifierLeft subjectRight classifierRight : RawTerm 0}
    (typingLeft : HasTypeDescPi profile TypingContext.empty subjectLeft classifierLeft)
    (typingRight : HasTypeDescPi profile TypingContext.empty subjectRight classifierRight) :
    Conv subjectLeft subjectRight ↔ typingLeft.normalForm = typingRight.normalForm :=
  RawTerm.normalize_eq_iff_conv subjectLeft subjectRight
    (HasTypeDescPi.closedStronglyNormalizing typingLeft)
    (HasTypeDescPi.closedStronglyNormalizing typingRight)

/-- **Decidable conversion of two closed grown-well-typed subjects, keyed on their derivations.**  Both
subjects are strongly normalizing by SN-043, so the parameter-free SN-fragment decider
`Conv.decidableOfStronglyNormalizing` decides their conversion — UNCONDITIONAL (no level-indexed hypothesis),
the grown-subject twin of the formation engine's `Conv.decidableOfHasTypeDesc`. -/
def HasTypeDescPi.closedConvDecidable {profile : PolyProfile}
    {subjectLeft classifierLeft subjectRight classifierRight : RawTerm 0}
    (typingLeft : HasTypeDescPi profile TypingContext.empty subjectLeft classifierLeft)
    (typingRight : HasTypeDescPi profile TypingContext.empty subjectRight classifierRight) :
    Decidable (Conv subjectLeft subjectRight) :=
  Conv.decidableOfStronglyNormalizing
    (HasTypeDescPi.closedStronglyNormalizing typingLeft)
    (HasTypeDescPi.closedStronglyNormalizing typingRight)

/-- **Non-vacuity: the typed normalizer does real reduction work.**  On the closed β-redex
`(λx. x) (Type@e)` — firing 64's `piElim` derivation `identityApplicationOnUniverseCode_hasTypeDescPi`,
typed at `Type@(e+1)` — the normalizer produces a normal form CONVERTIBLE to the redex's reduct `Type@e`
(`betaRedexConvertsToReduct` gives `Conv redex Type@e`; `normalForm_conv` gives `Conv redex normalForm`;
chain by `Conv.sym` + `Conv.trans`).  The normalizer is not classifying already-normal leaves — it contracts
a genuinely-typed redex. -/
theorem identityApplicationNormalForm_convReduct {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    Conv (universeCodeCell levelExpr flag)
      (identityApplicationOnUniverseCode_hasTypeDescPi
        (profile := profile) levelExpr flag).normalForm :=
  Conv.trans
    (Conv.sym (betaRedexConvertsToReduct levelExpr flag))
    (HasTypeDescPi.normalForm_conv _)

/-! ## The computed normal form IS the unique normal form (determinism connector)

`GrownTypeSafety.HasTypeDescPi.closedHasUniqueNormalForm` already proves, UNCONDITIONALLY, that a closed
grown-well-typed term has a unique normal form — but EXISTENTIALLY (there exists a value reached by every
reduction-to-normal-form).  These lemmas identify the COMPUTED `normalForm` above as exactly that unique
value: the normalizer does not merely produce *a* normal form, it produces *the* canonical one. -/

/-- **The computed normal form is THE unique normal form.**  Any normal form reachable from a closed
grown-well-typed subject equals `typing.normalForm` — both equal the unique value that
`closedHasUniqueNormalForm` asserts exists.  So the computed normalizer agrees with the abstract
determinism result: it computes the canonical normal form, not an arbitrary one. -/
theorem HasTypeDescPi.reachedNormalForm_eq_normalForm {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typing : HasTypeDescPi profile TypingContext.empty subject classifier)
    {reachedNormalForm : RawTerm 0}
    (reaches : StepStar subject reachedNormalForm)
    (reachedIsNormal : RawTerm.isStepNormalForm reachedNormalForm) :
    reachedNormalForm = typing.normalForm := by
  obtain ⟨_value, _, uniq⟩ := HasTypeDescPi.closedHasUniqueNormalForm typing
  exact (uniq reachedNormalForm reaches reachedIsNormal).trans
    (uniq typing.normalForm typing.normalForm_reducesTo typing.normalForm_isStepNormalForm).symm

/-- **Already-normal subjects are fixed points of the normalizer.**  If a closed grown-well-typed subject
is itself structurally normal, the normalizer returns it unchanged — the reflexive instance of
`reachedNormalForm_eq_normalForm`. -/
theorem HasTypeDescPi.normalForm_eq_self_of_isStepNormalForm {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typing : HasTypeDescPi profile TypingContext.empty subject classifier)
    (subjectIsNormal : RawTerm.isStepNormalForm subject) :
    typing.normalForm = subject :=
  (typing.reachedNormalForm_eq_normalForm (StepStar.refl subject) subjectIsNormal).symm

/-- Non-vacuity smoke: the identity `λx. x` (firing-63 derivation, already normal) normalizes to itself —
the normalizer is a genuine fixed point on a concrete grown-typed normal form (`by decide` confirms the
structural normality). -/
theorem identityNormalForm_eq {profile : PolyProfile} (levelExpr : LevelExpr) (flag : UniverseFlag) :
    (identityOnUniverse_hasTypeDescPi (profile := profile) levelExpr flag).normalForm =
      lamCell (universeCodeCell levelExpr flag) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) :=
  (identityOnUniverse_hasTypeDescPi (profile := profile) levelExpr flag).normalForm_eq_self_of_isStepNormalForm
    (lamCell_isStepNormalForm
      (rfl : RawTerm.isStepNormalForm (universeCodeCell levelExpr flag : RawTerm 0))
      (by decide))

end FX1Poly.Typed
