import FX1Poly.Typed.HasTypeDescBaseType
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.RawTermNF

/-! # FX1Poly/Typed/HasTypeDescBaseTypeMetatheory — inversion + determinism + SR/SN for the nullary
    base-type formation judgment (#1062 / DI-1b-meta: the structural metatheory of `HasTypeDescBaseType`).

Companion to `HasTypeDescBaseType` (the standalone nullary base-type formation judgment, #1061).  This
ships the metatheory the DI-4 / flat templates ship, plus the HEADLINE that the flag-pinning DESIGN
actually delivers — classifier determinism:

  * **`HasTypeDescBaseType.inversion`** — single-arm `cases` recovering the `baseFormation` fields.
  * **`baseTypeRuleDescOf_isBoolOrEmptyCode`** — the table holds exactly `gen_boolCode` / `gen_emptyCode`.
  * **`HasTypeDescBaseType.subjectIsBaseTypeCode` (★)** — a base-type-typed subject IS `boolTypeCell` or
    `emptyTypeCell`: the closed-FORMS content (the type-former twin of `subjectIsBoolConstructor`).
  * **`baseTypeRuleDescOf_outputIsType0`** — every tabled rule outputs `Type@0(standard)` (the flag is
    fixed in the rule — the load-bearing fact behind determinism).
  * **`HasTypeDescBaseType.classifierIsType0`** — a base-type classifier IS `Type@0(standard)`.
  * **`HasTypeDescBaseType.classifierDetermined` (★)** — two base-type derivations of the SAME subject
    have the SAME classifier (not merely `Conv` — EQUAL).  This is the PROOF that the flag-pinning design
    works: it is exactly the determinism that routing nullary formers through the flag-FREE generic
    `genFormation` arm would have BROKEN.  A clean corollary of `classifierIsType0` (each derivation pins
    `Type@0` independently — no `cases`-on-both, no dependent `mkGen`-index unification, hence propext-free).
  * **`HasTypeDescBaseType.subjectHasNoStep`** / **`subjectReduction`** / **`subjectStronglyNormalizing`** —
    the type-code cells are no-step LEAVES (`isStepNormalForm` by `rfl`), so SR is vacuous and the subject
    is strongly normalizing (the canonicity-relevant fact: a base type code is a normal form).

## Zero-axiom

Single-arm `cases` (mirroring `HasTypeDescDataIntro.inversion`, gated clean) + `by_cases` table
membership + `Option.some.inj` + `rfl` normality (`RawTerm.isStepNormalForm boolTypeCell/emptyTypeCell`)
+ `RawTerm.isStepNormalForm_blocks_step` + `isStronglyNormalizing_of_noStep` + `Eq.trans`/`Eq.symm`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Universe

/-- **Generic base-type inversion.**  A `HasTypeDescBaseType` derivation recovers its sole arm's fields:
the generator (a tabled nullary base type code), the payload/children, the rule, the subject as a `mkGen`
cell, and the classifier as the rule's `outputUniverse`.  Single-arm `cases` (the `context` is the auto-
index, so `cases` binds the five remaining fields). -/
theorem HasTypeDescBaseType.inversion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reachedClassifier : RawTerm scope}
    (derivation : HasTypeDescBaseType profile context subject reachedClassifier) :
    ∃ (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope) (rule : BaseTypeRuleDesc),
      baseTypeRuleDescOf generator = some rule ∧
      subject = .mkGen generator payload children ∧
      reachedClassifier = rule.outputUniverse scope := by
  cases derivation with
  | baseFormation generator payload children rule isBaseType =>
      exact ⟨generator, payload, children, rule, isBaseType, rfl, rfl⟩

/-- **The nullary base-type table holds exactly `boolCode` / `emptyCode` / `natCode` / `unitCode`.**
Any generator with a `baseTypeRuleDescOf` row is one of the four nullary base codes — `by_cases`
membership extraction (the base-type twin of `dataIntroNullaryRuleDescOf_isNullaryValueConstructor`).
Grows by one disjunct per future nullary base type code (`unitCode` landed exactly that way). -/
theorem baseTypeRuleDescOf_isNullaryBaseCode {generator : Generator} {rule : BaseTypeRuleDesc}
    (isBaseType : baseTypeRuleDescOf generator = some rule) :
    generator = .gen_boolCode ∨ generator = .gen_emptyCode ∨ generator = .gen_natCode ∨
      generator = .gen_unitCode := by
  by_cases hBool : generator = .gen_boolCode
  · exact Or.inl hBool
  · by_cases hEmpty : generator = .gen_emptyCode
    · exact Or.inr (Or.inl hEmpty)
    · by_cases hNat : generator = .gen_natCode
      · exact Or.inr (Or.inr (Or.inl hNat))
      · by_cases hUnit : generator = .gen_unitCode
        · exact Or.inr (Or.inr (Or.inr hUnit))
        · exfalso
          unfold baseTypeRuleDescOf at isBaseType
          rw [if_neg hBool, if_neg hEmpty, if_neg hNat, if_neg hUnit] at isBaseType
          contradiction

/-- **★ Closed forms for the base-type judgment: a typed subject is a base type code.**  Every term
typed by `HasTypeDescBaseType` is `boolTypeCell` or `emptyTypeCell` — the type-former twin of
`HasTypeDescDataIntro.subjectIsBoolConstructor`.  Cases the derivation, extracts the generator via the
table-membership lemma, and normalizes the cell by `cases payload` (`Unit` → `()`) + `cases children`
(`RawTermChildren []` → `childNil`), closing each branch by `rfl`. -/
theorem HasTypeDescBaseType.subjectIsBaseTypeCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescBaseType profile context subject classifier) :
    subject = boolTypeCell ∨ subject = emptyTypeCell ∨ subject = natTypeCell ∨
      subject = unitTypeCell := by
  cases derivation with
  | baseFormation generator payload children rule isBaseType =>
      rcases baseTypeRuleDescOf_isNullaryBaseCode isBaseType with hBool | hEmpty | hNat | hUnit
      · subst hBool
        cases payload
        cases children
        exact Or.inl rfl
      · subst hEmpty
        cases payload
        cases children
        exact Or.inr (Or.inl rfl)
      · subst hNat
        cases payload
        cases children
        exact Or.inr (Or.inr (Or.inl rfl))
      · subst hUnit
        cases payload
        cases children
        exact Or.inr (Or.inr (Or.inr rfl))

/-- **A base-type rule outputs `Type@0(standard)`.**  Every generator carrying a `baseTypeRuleDescOf`
row has `outputUniverse = fun _ => Type@0(standard)` — the flag is FIXED in the table, the load-bearing
fact behind classifier determinism.  The base-type twin of `typingRuleDescOf_outputIsUniverseFormer`. -/
theorem baseTypeRuleDescOf_outputIsType0 {generator : Generator} {rule : BaseTypeRuleDesc}
    (isBaseType : baseTypeRuleDescOf generator = some rule) :
    rule.outputUniverse = fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard := by
  rcases baseTypeRuleDescOf_isNullaryBaseCode isBaseType with hBool | hEmpty | hNat | hUnit
  · subst hBool
    rw [← Option.some.inj isBaseType]
  · subst hEmpty
    rw [← Option.some.inj isBaseType]
  · subst hNat
    rw [← Option.some.inj isBaseType]
  · subst hUnit
    rw [← Option.some.inj isBaseType]

/-- **Classifier inversion: a base-type classifier IS `Type@0(standard)`.**  The flag-pinned universe
code is the only classifier any base-type derivation reaches — recovered from the table via
`baseTypeRuleDescOf_outputIsType0`.  The classifier-side companion of `subjectIsBaseTypeCode`. -/
theorem HasTypeDescBaseType.classifierIsType0 {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescBaseType profile context subject classifier) :
    classifier = universeCodeCell LevelExpr.lzero UniverseFlag.standard := by
  cases derivation with
  | baseFormation generator payload children rule isBaseType =>
      rw [baseTypeRuleDescOf_outputIsType0 isBaseType]

/-- **★ Classifier determinism for the base-type judgment.**  Two base-type derivations of the SAME
subject reach the SAME classifier — not merely `Conv`-equal, EQUAL.  This is the concrete PROOF that the
flag-pinning design resolves the obstruction that blocked the generic-engine route: a free universe flag
would have let one subject acquire two distinct (`Type@0(standard)` vs another flag) non-`Conv`
classifiers, breaking uniqueness.  A clean corollary of `classifierIsType0` (each derivation pins
`Type@0` independently), so propext-free — no `cases`-on-both, no dependent `mkGen`-index unification. -/
theorem HasTypeDescBaseType.classifierDetermined {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier1 classifier2 : RawTerm scope}
    (firstDerivation : HasTypeDescBaseType profile context subject classifier1)
    (secondDerivation : HasTypeDescBaseType profile context subject classifier2) :
    classifier1 = classifier2 :=
  firstDerivation.classifierIsType0.trans secondDerivation.classifierIsType0.symm

/-- **No-step substrate: a base-type subject blocks every `Step`.**  Its subject is a base type code
(`subjectIsBaseTypeCode`: one of the four nullary base codes), each of which is a no-step LEAF
(`RawTerm.isStepNormalForm` by `rfl` — childless, non-redex head), and a normal form blocks every step
(`RawTerm.isStepNormalForm_blocks_step`).  The shared ingredient of SR and SN below. -/
theorem HasTypeDescBaseType.subjectHasNoStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescBaseType profile context subject classifier)
    (targetTerm : RawTerm scope) : ¬ Step subject targetTerm := by
  rcases derivation.subjectIsBaseTypeCode with hBool | hEmpty | hNat | hUnit
  · rw [hBool]
    exact RawTerm.isStepNormalForm_blocks_step
      (rfl : RawTerm.isStepNormalForm (boolTypeCell : RawTerm scope)) targetTerm
  · rw [hEmpty]
    exact RawTerm.isStepNormalForm_blocks_step
      (rfl : RawTerm.isStepNormalForm (emptyTypeCell : RawTerm scope)) targetTerm
  · rw [hNat]
    exact RawTerm.isStepNormalForm_blocks_step
      (rfl : RawTerm.isStepNormalForm (natTypeCell : RawTerm scope)) targetTerm
  · rw [hUnit]
    exact RawTerm.isStepNormalForm_blocks_step
      (rfl : RawTerm.isStepNormalForm (unitTypeCell : RawTerm scope)) targetTerm

/-- **Subject reduction for the base-type judgment (vacuous: type codes do not reduce).**  A base-type
subject is a no-step leaf, so there is no `reduct` to preserve typing for — `subjectHasNoStep` refutes
the step.  The true content of SR for nullary type formers. -/
theorem HasTypeDescBaseType.subjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reduct classifier : RawTerm scope}
    (derivation : HasTypeDescBaseType profile context subject classifier)
    (step : Step subject reduct) :
    HasTypeDescBaseType profile context reduct classifier :=
  (derivation.subjectHasNoStep reduct step).elim

/-- **★ Strong normalization of a base-type subject.**  A base-type-typed term is strongly normalizing —
immediate from the no-step substrate via `isStronglyNormalizing_of_noStep`.  The canonicity-relevant fact:
a base type code is a normal form. -/
theorem HasTypeDescBaseType.subjectStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescBaseType profile context subject classifier) :
    IsStronglyNormalizing subject :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => derivation.subjectHasNoStep targetTerm step)

end FX1Poly.Typed
