import FX1Poly.Typed.FormerStepInversionGeneric
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Core.ConvNormalForm

/-! # FX1Poly/Typed/ConvFormationFormerRigidity — the CASCADE-FREE cross-former `Conv` discrimination
    (table-generic "no confusion" for formation-table type-code formers).

The per-pair rigidity (`ConvCodeInjectivity`'s `piTyCode_not_sigmaTyCode` / `…_not_universeCode`,
`ConvBoolCodeRigidity`, `EmptyTypeCodeConvRigidity`) discriminates ENUMERATED former pairs.  This file
ships the TABLE-GENERIC version: distinct formation-table formers (any two generators carrying a
`typingRuleDescOf` row) are never convertible — proven WITHOUT naming a single generator, so every future
formation row is absorbed ZERO-TOUCH.

## The cascade-free payoff

The generic discrimination covers exactly the `typingRuleDescOf`-formers (today
`{piTyCode, sigmaTyCode, listCode, optionCode}`).  It is the rigidity twin of the cascade-free
`formerCellStepIsChildCongruence` (TG-1): a step out of a formation cell preserves the head, so a `Conv`
join of two formation cells forces a shared head — `headGenerator`-equal, hence the same generator.  The
crucial consequence: the MOMENT a new formation row lands (the `gen_boolCode` row of DI-1b, a cubical /
HIT type code, an IR code), that former AUTOMATICALLY gets ALL its cross-former rule-outs from this one
theorem — no per-pair lemma needed.  This is the canonicity rule-out substrate made cascade-free.

## Contents

* `StepStar.formationFormerHeadStableGeneral` — generic head-stability: a reduction out of a formation cell
  preserves the head generator and payload, reducing only the children (lifts `formerCellStepIsChildCongruence`
  through `StepStar`, no generator named).
* `Conv.formationFormerGeneratorEq` — convertible formation cells have the SAME generator (both reduce to a
  shared common reduct whose head is forced to each former's generator).
* `Conv.formationFormersNotConvOfDistinct` — distinct formation generators are never convertible (the
  contrapositive — the rule-out form).
* `Conv.listCode_not_conv_optionCode` — a concrete NEW discrimination (not previously shipped): `List A` is
  never convertible to `Option B`, for arbitrary payloads/children, as a `by`-free instance of the generic
  theorem (the non-vacuity witness).

## Zero-axiom

`formerCellStepIsChildCongruence` + `StepStar` induction + the `Conv`/`Join` unpack + `congrArg
RawTerm.headGenerator` + `Generator.noConfusion`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Generic head-stability under `StepStar`.**  A reduction out of any cell whose head carries a formation
rule preserves the head generator AND payload, reducing only the children — proven without naming a single
generator (lifts `formerCellStepIsChildCongruence` through `StepStar` induction).  The table-generic twin of
`StepStar.shapeStable_piTyCode`. -/
theorem StepStar.formationFormerHeadStableGeneral {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) :
    ∀ (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope) (rule : TypingRuleDesc),
      source = .mkGen generator payload children → typingRuleDescOf generator = some rule →
      ∃ children', target = .mkGen generator payload children' := by
  induction chain with
  | refl _term =>
      intro generator payload children _rule sourceEq _isFormation
      exact ⟨children, sourceEq⟩
  | trans headStep _tail tailIH =>
      intro generator payload children rule sourceEq isFormation
      subst sourceEq
      obtain ⟨childrenMid, midEq, _childStep⟩ := formerCellStepIsChildCongruence isFormation headStep
      exact tailIH generator payload childrenMid rule midEq isFormation

/-- **Convertible formation formers have the same generator.**  Both sides of a `Conv` reduce to a shared
common reduct; head-stability pins the common reduct's head to EACH former's generator, so the generators
agree (`congrArg RawTerm.headGenerator`).  Table-generic — no generator is enumerated. -/
theorem Conv.formationFormerGeneratorEq {scope : Nat} {firstGenerator secondGenerator : Generator}
    {firstPayload : firstGenerator.payload scope}
    {firstChildren : RawTermChildren firstGenerator.binderShifts scope}
    {secondPayload : secondGenerator.payload scope}
    {secondChildren : RawTermChildren secondGenerator.binderShifts scope}
    {firstRule secondRule : TypingRuleDesc}
    (convertibility :
      Conv (.mkGen firstGenerator firstPayload firstChildren)
        (.mkGen secondGenerator secondPayload secondChildren))
    (firstIsFormation : typingRuleDescOf firstGenerator = some firstRule)
    (secondIsFormation : typingRuleDescOf secondGenerator = some secondRule) :
    firstGenerator = secondGenerator := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨_firstChildrenAfter, leftEq⟩ :=
    StepStar.formationFormerHeadStableGeneral leftChain firstGenerator firstPayload firstChildren
      firstRule rfl firstIsFormation
  obtain ⟨_secondChildrenAfter, rightEq⟩ :=
    StepStar.formationFormerHeadStableGeneral rightChain secondGenerator secondPayload secondChildren
      secondRule rfl secondIsFormation
  rw [leftEq] at rightEq
  exact congrArg RawTerm.headGenerator rightEq

/-- **Distinct formation formers are never convertible** (the rule-out form).  The contrapositive of
`formationFormerGeneratorEq`: if the generators differ, no conversion exists.  Once a new formation row lands,
that former gets all its cross-former rule-outs from this one theorem. -/
theorem Conv.formationFormersNotConvOfDistinct {scope : Nat}
    {firstGenerator secondGenerator : Generator}
    {firstPayload : firstGenerator.payload scope}
    {firstChildren : RawTermChildren firstGenerator.binderShifts scope}
    {secondPayload : secondGenerator.payload scope}
    {secondChildren : RawTermChildren secondGenerator.binderShifts scope}
    {firstRule secondRule : TypingRuleDesc}
    (distinct : firstGenerator ≠ secondGenerator)
    (firstIsFormation : typingRuleDescOf firstGenerator = some firstRule)
    (secondIsFormation : typingRuleDescOf secondGenerator = some secondRule) :
    ¬ Conv (.mkGen firstGenerator firstPayload firstChildren)
        (.mkGen secondGenerator secondPayload secondChildren) :=
  fun convertibility =>
    distinct (Conv.formationFormerGeneratorEq convertibility firstIsFormation secondIsFormation)

/-- **Concrete non-vacuity: `List` is never convertible to `Option`.**  A new discrimination (the per-pair
files cover Π/Σ/universe/empty/bool but not list-vs-option), here a `by`-free instance of the generic theorem
over arbitrary payloads/children — `gen_listCode ≠ gen_optionCode` (`Generator.noConfusion`) plus the two
shipped `rfl` formation rows. -/
theorem Conv.listCode_not_conv_optionCode {scope : Nat}
    {listPayload : Generator.gen_listCode.payload scope}
    {listChildren : RawTermChildren Generator.gen_listCode.binderShifts scope}
    {optionPayload : Generator.gen_optionCode.payload scope}
    {optionChildren : RawTermChildren Generator.gen_optionCode.binderShifts scope}
    (convertibility :
      Conv (.mkGen .gen_listCode listPayload listChildren)
        (.mkGen .gen_optionCode optionPayload optionChildren)) :
    False :=
  Conv.formationFormersNotConvOfDistinct
    (fun headsEqual => Generator.noConfusion headsEqual)
    typingRuleDescOf_listCode typingRuleDescOf_optionCode convertibility

end FX1Poly.Typed
