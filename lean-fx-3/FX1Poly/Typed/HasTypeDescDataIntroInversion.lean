import FX1Poly.Typed.HasTypeDescDataIntro

/-! # FX1Poly/Typed/HasTypeDescDataIntroInversion — inversion + bool canonical forms for the
    data-CONSTRUCTOR judgment (DI-1 / DI-4 inversion slice).

Companion to `HasTypeDescDataIntro` (the standalone data-constructor typing judgment, DI-1).  Its
metatheory needs the same inversion the formation / flat engines have, and — crucially for typed
canonicity (link-4) — the CLOSED-CANONICAL-FORMS fact: a term typed by the data-intro judgment is one
of the data constructors.  For the current nullary-bool judgment that is exactly `boolTrue` or
`boolFalse`.

This is the data-intro twin of `HasTypeDescFlatInversion`:

  * `HasTypeDescDataIntro.inversion` — single-arm `cases` recovering the `nullaryIntro` fields
    (generator + table witness + subject-as-`mkGen` + classifier-as-`outputTypeCode`).
  * `dataIntroNullaryRuleDescOf_isBoolConstructor` — the table currently holds exactly the two bool
    constructors (`by_cases` membership extraction, the twin of `flatFormationRuleImpliesNotVariable`).
  * **`HasTypeDescDataIntro.subjectIsBoolConstructor` (★)** — a data-intro-typed subject IS
    `boolTrueCell` or `boolFalseCell`: the closed-canonical-forms content the bool-canonicity rule-out
    (CANON-1) consumes.  As more constructors land (`pair`/`either` — DI-2; `natSucc`/`listCons` —
    DI-3), this REFINES to a wider disjunction; over the present nullary-bool judgment it pins exactly
    the two bool constructors.

## Zero-axiom

`inversion` is a single-arm `cases` + `exact` (the `nullaryIntro` `context` is the auto-index, so
`cases` binds exactly the five remaining fields).  `subjectIsBoolConstructor` cases the derivation,
extracts the generator via the table-membership lemma, and normalizes the cell by `cases payload`
(`Generator.payload gen_boolTrue` reduces to `Unit` → `()`) + `cases children` (`RawTermChildren []`
→ `childNil`), closing each branch by `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Generic data-intro inversion.**  A `HasTypeDescDataIntro` derivation recovers its sole arm's
fields: the generator (a tabled nullary constructor), the payload/children, the rule, the subject as a
`mkGen` cell, and the classifier as the rule's `outputTypeCode`.  Single-arm `cases` over the
one-constructor judgment (the `context` is the auto-index, so `cases` binds the five remaining fields). -/
theorem HasTypeDescDataIntro.inversion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reachedClassifier : RawTerm scope}
    (derivation : HasTypeDescDataIntro profile context subject reachedClassifier) :
    ∃ (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope) (rule : DataIntroNullaryRuleDesc),
      dataIntroNullaryRuleDescOf generator = some rule ∧
      subject = .mkGen generator payload children ∧
      reachedClassifier = rule.outputTypeCode scope := by
  cases derivation with
  | nullaryIntro generator payload children rule isDataIntro =>
      exact ⟨generator, payload, children, rule, isDataIntro, rfl, rfl⟩

/-- **The nullary data-intro table holds exactly the bool constructors and the unit value.**  Any
generator with a `dataIntroNullaryRuleDescOf` row is `gen_boolTrue`, `gen_boolFalse`, or `gen_unit`
— `by_cases` membership extraction, the data-intro twin of `flatFormationRuleImpliesNotVariable`.
Grows by one disjunct per future nullary-constructor row (`gen_unit` landed exactly that way). -/
theorem dataIntroNullaryRuleDescOf_isNullaryValueConstructor {generator : Generator}
    {rule : DataIntroNullaryRuleDesc}
    (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule) :
    generator = .gen_boolTrue ∨ generator = .gen_boolFalse ∨ generator = .gen_unit := by
  by_cases hTrue : generator = .gen_boolTrue
  · exact Or.inl hTrue
  · by_cases hFalse : generator = .gen_boolFalse
    · exact Or.inr (Or.inl hFalse)
    · by_cases hUnit : generator = .gen_unit
      · exact Or.inr (Or.inr hUnit)
      · exfalso
        unfold dataIntroNullaryRuleDescOf at isDataIntro
        rw [if_neg hTrue, if_neg hFalse, if_neg hUnit] at isDataIntro
        contradiction

/-- **★ Closed canonical forms for the data-intro judgment: a typed subject is a bool constructor.**
Every term typed by `HasTypeDescDataIntro` is `boolTrueCell` or `boolFalseCell` — the closed-
canonical-forms content the bool-canonicity rule-out (CANON-1, the link-4 gap) consumes: combined with
strong normalization + subject reduction, it yields "closed `t : boolCode` reduces to `boolTrue` or
`boolFalse`".  Over the present nullary-bool judgment it pins exactly the two bool constructors; it
refines to a wider disjunction as DI-2/DI-3 add constructors. -/
theorem HasTypeDescDataIntro.subjectIsNullaryValueCell {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescDataIntro profile context subject classifier) :
    subject = boolTrueCell ∨ subject = boolFalseCell ∨ subject = unitCell := by
  cases derivation with
  | nullaryIntro generator payload children rule isDataIntro =>
      rcases dataIntroNullaryRuleDescOf_isNullaryValueConstructor isDataIntro with
        hTrue | hFalse | hUnit
      · subst hTrue
        cases payload
        cases children
        exact Or.inl rfl
      · subst hFalse
        cases payload
        cases children
        exact Or.inr (Or.inl rfl)
      · subst hUnit
        cases payload
        cases children
        exact Or.inr (Or.inr rfl)

end FX1Poly.Typed
