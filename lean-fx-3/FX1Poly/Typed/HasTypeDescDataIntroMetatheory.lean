import FX1Poly.Typed.HasTypeDescDataIntroInversion
import FX1Poly.Typed.RawTermHeadGenerator
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

/-- **No-step substrate: a data-intro subject blocks every `Step`.**  Its subject is a nullary value
cell (`subjectIsNullaryValueCell`: a bool constructor or the unit value), each a childless non-redex
LEAF (`RawTerm.isStepNormalForm` by `rfl`), and a normal form blocks every step
(`RawTerm.isStepNormalForm_blocks_step`).  The shared ingredient of SR and SN below. -/
theorem HasTypeDescDataIntro.subjectHasNoStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescDataIntro profile context subject classifier)
    (targetTerm : RawTerm scope) : ¬ Step subject targetTerm := by
  rcases derivation.subjectIsNullaryValueCell with
    hTrue | hFalse | hUnit | hZero | hOne | hNatZero
  · rw [hTrue]
    exact RawTerm.isStepNormalForm_blocks_step
      (rfl : RawTerm.isStepNormalForm (boolTrueCell : RawTerm scope)) targetTerm
  · rw [hFalse]
    exact RawTerm.isStepNormalForm_blocks_step
      (rfl : RawTerm.isStepNormalForm (boolFalseCell : RawTerm scope)) targetTerm
  · rw [hUnit]
    exact RawTerm.isStepNormalForm_blocks_step
      (rfl : RawTerm.isStepNormalForm (unitCell : RawTerm scope)) targetTerm
  · rw [hZero]
    exact RawTerm.isStepNormalForm_blocks_step
      (rfl : RawTerm.isStepNormalForm (intervalZeroValueCell : RawTerm scope)) targetTerm
  · rw [hOne]
    exact RawTerm.isStepNormalForm_blocks_step
      (rfl : RawTerm.isStepNormalForm (intervalOneValueCell : RawTerm scope)) targetTerm
  · rw [hNatZero]
    exact RawTerm.isStepNormalForm_blocks_step
      (rfl : RawTerm.isStepNormalForm (natZeroCell : RawTerm scope)) targetTerm

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

/-- **Classifier inversion: a data-intro classifier is `boolTypeCell` or `unitTypeCell`.**  The twin
of `subjectIsNullaryValueCell` on the classifier side: cases the derivation, identifies the generator
via the table-membership lemma, and recovers the rule from the table diagonal (`Option.some.inj`).
The classifier-side companion the canonicity rule-outs consume alongside the subject side. -/
theorem HasTypeDescDataIntro.classifierIsNullaryTypeCell {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescDataIntro profile context subject classifier) :
    classifier = boolTypeCell ∨ classifier = unitTypeCell ∨ classifier = intervalTypeCell ∨
      classifier = natTypeCell := by
  cases derivation with
  | nullaryIntro generator payload children rule isDataIntro =>
      rcases dataIntroNullaryRuleDescOf_isNullaryValueConstructor isDataIntro with
        hTrue | hFalse | hUnit | hZero | hOne | hNatZero
      · subst hTrue
        have hrule : rule = { outputTypeCode := fun _ => boolTypeCell } :=
          (Option.some.inj isDataIntro).symm
        exact Or.inl (by rw [hrule])
      · subst hFalse
        have hrule : rule = { outputTypeCode := fun _ => boolTypeCell } :=
          (Option.some.inj isDataIntro).symm
        exact Or.inl (by rw [hrule])
      · subst hUnit
        have hrule : rule = { outputTypeCode := fun _ => unitTypeCell } :=
          (Option.some.inj isDataIntro).symm
        exact Or.inr (Or.inl (by rw [hrule]))
      · subst hZero
        have hrule : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
          (Option.some.inj isDataIntro).symm
        exact Or.inr (Or.inr (Or.inl (by rw [hrule])))
      · subst hOne
        have hrule : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
          (Option.some.inj isDataIntro).symm
        exact Or.inr (Or.inr (Or.inl (by rw [hrule])))
      · subst hNatZero
        have hrule : rule = { outputTypeCode := fun _ => natTypeCell } :=
          (Option.some.inj isDataIntro).symm
        exact Or.inr (Or.inr (Or.inr (by rw [hrule])))

/-- **Subject/classifier coordination for the nullary data-intro rows.**  One `cases` pass yields the
exact (subject, classifier) PAIR for each table row — the bool constructors at `boolTypeCell`, the
unit value at `unitTypeCell`.  Sharper than the separate subject/classifier inversions (which lose
the row correlation); the unit-canonicity corollary below needs exactly this coordination. -/
theorem HasTypeDescDataIntro.subjectClassifierCoordinated {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescDataIntro profile context subject classifier) :
    (subject = boolTrueCell ∧ classifier = boolTypeCell) ∨
      (subject = boolFalseCell ∧ classifier = boolTypeCell) ∨
      (subject = unitCell ∧ classifier = unitTypeCell) ∨
      (subject = intervalZeroValueCell ∧ classifier = intervalTypeCell) ∨
      (subject = intervalOneValueCell ∧ classifier = intervalTypeCell) ∨
      (subject = natZeroCell ∧ classifier = natTypeCell) := by
  cases derivation with
  | nullaryIntro generator payload children rule isDataIntro =>
      rcases dataIntroNullaryRuleDescOf_isNullaryValueConstructor isDataIntro with
        hTrue | hFalse | hUnit | hZero | hOne | hNatZero
      · subst hTrue
        have hrule : rule = { outputTypeCode := fun _ => boolTypeCell } :=
          (Option.some.inj isDataIntro).symm
        cases payload
        cases children
        exact Or.inl ⟨rfl, by rw [hrule]⟩
      · subst hFalse
        have hrule : rule = { outputTypeCode := fun _ => boolTypeCell } :=
          (Option.some.inj isDataIntro).symm
        cases payload
        cases children
        exact Or.inr (Or.inl ⟨rfl, by rw [hrule]⟩)
      · subst hUnit
        have hrule : rule = { outputTypeCode := fun _ => unitTypeCell } :=
          (Option.some.inj isDataIntro).symm
        cases payload
        cases children
        exact Or.inr (Or.inr (Or.inl ⟨rfl, by rw [hrule]⟩))
      · subst hZero
        have hrule : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
          (Option.some.inj isDataIntro).symm
        cases payload
        cases children
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by rw [hrule]⟩)))
      · subst hOne
        have hrule : rule = { outputTypeCode := fun _ => intervalTypeCell } :=
          (Option.some.inj isDataIntro).symm
        cases payload
        cases children
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by rw [hrule]⟩))))
      · subst hNatZero
        have hrule : rule = { outputTypeCode := fun _ => natTypeCell } :=
          (Option.some.inj isDataIntro).symm
        cases payload
        cases children
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by rw [hrule]⟩))))

/-- **★ Unit canonical form at the data-intro engine: a subject typed at `unitTypeCell` IS the unit
value.**  The classifier discriminates the table rows syntactically (`unitTypeCell` and `boolTypeCell`
have distinct head generators, refuted by `Generator.noConfusion`), so typed-at-`unitTypeCell` forces the
`gen_unit` row — the one-value collapse the typed unit-eta judgment is built on. -/
theorem HasTypeDescDataIntro.subjectIsUnitOfUnitClassifier {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    (derivation : HasTypeDescDataIntro profile context subject unitTypeCell) :
    subject = unitCell := by
  rcases derivation.subjectClassifierCoordinated with
    ⟨_, hClassifier⟩ | ⟨_, hClassifier⟩ | ⟨hSubject, _⟩ | ⟨_, hClassifier⟩ | ⟨_, hClassifier⟩
      | ⟨_, hClassifier⟩
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator hClassifier)
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator hClassifier)
  · exact hSubject
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator hClassifier)
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator hClassifier)
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator hClassifier)

end FX1Poly.Typed
