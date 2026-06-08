import FX1Poly.Typed.HasTypeDescDataIntroInversion
import FX1Poly.Core.BoolCanonicalFormsCandidate
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.RawTermNF

/-! # FX1Poly/Typed/HasTypeDescDataIntroMetatheory — subject reduction + strong normalization for the
    data-CONSTRUCTOR judgment (DI-4: the substantive SR/SN half of the structural quartet).

Companion to `HasTypeDescDataIntro` (the standalone data-constructor typing judgment) and its inversion
slice (`HasTypeDescDataIntroInversion`).  The flat-engine template ships a four-part structural quartet
(SR / weakening / substitution / SN).  For the data-intro judgment two of those four are SUBSTANTIVE and
two are DEGENERATE, and this file ships the substantive pair plus the classifier-inversion companion:

  * **`HasTypeDescDataIntro.subjectHasNoStep`** — the shared substrate: a data-intro subject blocks every
    `Step` (it is a bool VALUE, hence a structural normal form).  Built directly from
    `subjectIsBoolConstructor` (the inversion slice) — which is definitionally exactly `boolIsValue` of the
    subject — composed with `boolIsValue_impliesStepNormalForm` and `RawTerm.isStepNormalForm_blocks_step`.
  * **`HasTypeDescDataIntro.subjectReduction`** — SR: `Step subject reduct → HasTypeDescDataIntro … reduct …`.
    Vacuously true because the subject is a normal-form value (there is no `reduct`); this is the TRUE
    content of SR for data constructors, not a shortcut — values have nothing to reduce.
  * **`HasTypeDescDataIntro.subjectStronglyNormalizing`** — SN: the subject is strongly normalizing, via
    `isStronglyNormalizing_of_noStep` applied to the no-step substrate.  This is the canonicity-relevant
    fact: a closed data-intro-typed term is a normal-form value.
  * **`HasTypeDescDataIntro.classifierIsBoolTypeCell`** — the classifier twin of `subjectIsBoolConstructor`:
    a data-intro classifier IS `boolTypeCell`.  Recovers the rule from the table by `Option.some.inj`.

## Why weakening / substitution are DEGENERATE here (deferred to DI-2)

The remaining two quartet members — renaming/weakening and substitution stability — are vacuous for the
present nullary-bool judgment: its subjects (`boolTrueCell` / `boolFalseCell`) and classifier
(`boolTypeCell`) are CLOSED cells (no free variables, `binderShifts = []`), so any renaming or
substitution acts as the identity on them, and the universe-polymorphic intro smokes
(`HasTypeDescDataIntro.boolTrueTyped` / `boolFalseTyped`, which hold at EVERY scope and context) already
witness structural stability by construction.  Weakening/substitution become SUBSTANTIVE only once the
n-ary constructor arm (DI-2: `pair` / `eitherInl` / `eitherInr`) gives the judgment subjects whose
children mention variables — there they are folded in on the flat template's
`renameRespectingContext` / `substRespectingContext` shape.

## Zero-axiom

Every theorem is a direct composition of shipped Core lemmas + the inversion slice — no induction, no
`cases` beyond `classifierIsBoolTypeCell`'s single-arm recovery.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Universe

/-- **No-step substrate: a data-intro subject blocks every `Step`.**  Its subject is a bool value
(`subjectIsBoolConstructor`, which is definitionally `boolIsValue` of the subject), bool values are
structural normal forms (`boolIsValue_impliesStepNormalForm`), and a normal form blocks every step
(`RawTerm.isStepNormalForm_blocks_step`).  The shared ingredient of SR and SN below. -/
theorem HasTypeDescDataIntro.subjectHasNoStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescDataIntro profile context subject classifier)
    (targetTerm : RawTerm scope) : ¬ Step subject targetTerm :=
  RawTerm.isStepNormalForm_blocks_step
    (boolIsValue_impliesStepNormalForm derivation.subjectIsBoolConstructor) targetTerm

/-- **Subject reduction for the data-intro judgment (vacuous: values do not reduce).**  A data-intro
subject is a normal-form value, so there is no `reduct` to preserve typing for — `subjectHasNoStep`
refutes the step.  This is the true content of SR for data constructors. -/
theorem HasTypeDescDataIntro.subjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reduct classifier : RawTerm scope}
    (derivation : HasTypeDescDataIntro profile context subject classifier)
    (step : Step subject reduct) :
    HasTypeDescDataIntro profile context reduct classifier :=
  (derivation.subjectHasNoStep reduct step).elim

/-- **★ Strong normalization of a data-intro subject.**  A data-intro-typed term is strongly normalizing
— immediate from the no-step substrate via `isStronglyNormalizing_of_noStep`.  The canonicity-relevant
metatheory fact: a closed data-intro-typed term is a normal-form value. -/
theorem HasTypeDescDataIntro.subjectStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescDataIntro profile context subject classifier) :
    IsStronglyNormalizing subject :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => derivation.subjectHasNoStep targetTerm step)

/-- **Classifier inversion: a data-intro classifier IS `boolTypeCell`.**  The twin of
`subjectIsBoolConstructor` on the classifier side: cases the derivation, identifies the generator as a
bool constructor (`dataIntroNullaryRuleDescOf_isBoolConstructor`), and recovers the rule from the table
diagonal (`Option.some.inj`), so the reached classifier `rule.outputTypeCode scope` is `boolTypeCell`.
The classifier-side companion the bool-canonicity rule-out (CANON-1) consumes alongside the subject side. -/
theorem HasTypeDescDataIntro.classifierIsBoolTypeCell {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescDataIntro profile context subject classifier) :
    classifier = boolTypeCell := by
  cases derivation with
  | nullaryIntro generator payload children rule isDataIntro =>
      rcases dataIntroNullaryRuleDescOf_isBoolConstructor isDataIntro with hTrue | hFalse
      · subst hTrue
        have hrule : rule = { outputTypeCode := fun _ => boolTypeCell } :=
          (Option.some.inj isDataIntro).symm
        rw [hrule]
      · subst hFalse
        have hrule : rule = { outputTypeCode := fun _ => boolTypeCell } :=
          (Option.some.inj isDataIntro).symm
        rw [hrule]

end FX1Poly.Typed
