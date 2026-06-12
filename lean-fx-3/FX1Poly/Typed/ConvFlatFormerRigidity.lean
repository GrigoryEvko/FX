import FX1Poly.Typed.NativeUnionRuleTables
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Core.ConvNormalForm

/-! # FX1Poly/Typed/ConvFlatFormerRigidity — the CASCADE-FREE cross-former `Conv` discrimination for the
    FLAT data type-code formers (the flat-table twin of `ConvFormationFormerRigidity`).

`ConvFormationFormerRigidity` shipped the table-generic cross-former rigidity for the `typingRuleDescOf`-formers
(the dependent binders Π / Σ plus the unary data codes list / option).  This file ships the IDENTICAL
construction keyed on the FLAT table (`flatTypingRuleDescOf`), covering the binary non-dependent data
type-code formers `product` / `sum` / `either` / `arrow` / `equiv` — so the two files TOGETHER give the
complete cross-former "no confusion" for every data type-code former.

## Why the flat formers need their own file

The flat formers carry NO `typingRuleDescOf` row (they are typed by the union's `flatFormation` arm over
`flatTypingRuleDescOf`), so `formerCellStepIsChildCongruence` (keyed on `typingRuleDescOf`) does not apply to
them.  The local `flatFormerCellStepIsChildCongruence` below is the exact flat analogue
(a flat-former cell heads no root redex, so any step out of it is a child congruence) — so the same SN-free
head-stability argument runs verbatim on the flat table.  These rigidities feed the data-canonicity rule-outs
for `pair` / `sum` / `either` (SN-049): a closed normal `t : productCode A B` cannot be classified by a
distinct flat former.

## Contents

* `StepStar.flatFormationFormerHeadStableGeneral` — generic head-stability under `StepStar`, no flat generator
  named (lifts `flatFormerCellStepIsChildCongruence`).
* `Conv.flatFormationFormerGeneratorEq` — convertible flat formers share the generator.
* `Conv.flatFormationFormersNotConvOfDistinct` — distinct flat formers are never convertible.
* `Conv.productCode_not_conv_sumCode` — a concrete NEW discrimination (`A × B` is never `A + B`), a `by`-free
  instance over arbitrary payloads/children (the non-vacuity witness).

## Zero-axiom

`flatFormerCellStepIsChildCongruence` + `StepStar` induction + the `Conv`/`Join` unpack + `congrArg
RawTerm.headGenerator` + `Generator.noConfusion`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Flat-former step inversion.**  A flat-former cell heads no root redex, so any `Step` out of it is a child
congruence.  Keyed on the FLAT table (`flatTypingRuleDescOf`): each redex head has `flatTypingRuleDescOf = none`
by rfl, so the `some rule` hypothesis contradicts every redex arm; only the `cong` arm survives, exposing the
child step directly.  A `Step`/table-only fact (no typing engine), ported verbatim so this file no longer
depends on the flat typing engine. -/
private theorem flatFormerCellStepIsChildCongruence {scope : Nat} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {rule : TypingRuleDesc} {target : RawTerm scope}
    (isFlatFormation : flatTypingRuleDescOf generator = some rule)
    (step : Step (.mkGen generator payload children) target) :
    ∃ children', target = .mkGen generator payload children' ∧ StepChildren children children' := by
  cases step with
  | cong _ _ childStep => exact ⟨_, rfl, childStep⟩
  | beta => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaBoolTrue => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaBoolFalse => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaFstPair => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaSndPair => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaNatElimZero => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaNatRecZero => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaListElimNil => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaOptionMatchNone => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaOptionMatchSome => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaEitherMatchInl => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaEitherMatchInr => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaNatElimSucc => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaNatRecSucc => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaListElimCons => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaIdJRefl => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)
  | iotaIdStrictRecRefl => nomatch (show (none : Option TypingRuleDesc) = some rule from isFlatFormation)

/-- **Generic head-stability under `StepStar` for the FLAT formers.**  A reduction out of any cell whose head
carries a FLAT formation rule preserves the head generator AND payload, reducing only the children — no flat
generator named (lifts `flatFormerCellStepIsChildCongruence` through `StepStar` induction). -/
theorem StepStar.flatFormationFormerHeadStableGeneral {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) :
    ∀ (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope) (rule : TypingRuleDesc),
      source = .mkGen generator payload children → flatTypingRuleDescOf generator = some rule →
      ∃ children', target = .mkGen generator payload children' := by
  induction chain with
  | refl _term =>
      intro generator payload children _rule sourceEq _isFlatFormation
      exact ⟨children, sourceEq⟩
  | trans headStep _tail tailIH =>
      intro generator payload children rule sourceEq isFlatFormation
      subst sourceEq
      obtain ⟨childrenMid, midEq, _childStep⟩ :=
        flatFormerCellStepIsChildCongruence isFlatFormation headStep
      exact tailIH generator payload childrenMid rule midEq isFlatFormation

/-- **Convertible flat formers have the same generator.**  Both sides reduce to a shared common reduct whose
head is forced to each flat former's generator (`congrArg RawTerm.headGenerator`). -/
theorem Conv.flatFormationFormerGeneratorEq {scope : Nat} {firstGenerator secondGenerator : Generator}
    {firstPayload : firstGenerator.payload scope}
    {firstChildren : RawTermChildren firstGenerator.binderShifts scope}
    {secondPayload : secondGenerator.payload scope}
    {secondChildren : RawTermChildren secondGenerator.binderShifts scope}
    {firstRule secondRule : TypingRuleDesc}
    (convertibility :
      Conv (.mkGen firstGenerator firstPayload firstChildren)
        (.mkGen secondGenerator secondPayload secondChildren))
    (firstIsFlatFormation : flatTypingRuleDescOf firstGenerator = some firstRule)
    (secondIsFlatFormation : flatTypingRuleDescOf secondGenerator = some secondRule) :
    firstGenerator = secondGenerator := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨_firstChildrenAfter, leftEq⟩ :=
    StepStar.flatFormationFormerHeadStableGeneral leftChain firstGenerator firstPayload firstChildren
      firstRule rfl firstIsFlatFormation
  obtain ⟨_secondChildrenAfter, rightEq⟩ :=
    StepStar.flatFormationFormerHeadStableGeneral rightChain secondGenerator secondPayload secondChildren
      secondRule rfl secondIsFlatFormation
  rw [leftEq] at rightEq
  exact congrArg RawTerm.headGenerator rightEq

/-- **Distinct flat formers are never convertible** (the rule-out form).  The contrapositive of
`flatFormationFormerGeneratorEq` — every new flat formation row gets all its cross-former rule-outs from this
one theorem. -/
theorem Conv.flatFormationFormersNotConvOfDistinct {scope : Nat}
    {firstGenerator secondGenerator : Generator}
    {firstPayload : firstGenerator.payload scope}
    {firstChildren : RawTermChildren firstGenerator.binderShifts scope}
    {secondPayload : secondGenerator.payload scope}
    {secondChildren : RawTermChildren secondGenerator.binderShifts scope}
    {firstRule secondRule : TypingRuleDesc}
    (distinct : firstGenerator ≠ secondGenerator)
    (firstIsFlatFormation : flatTypingRuleDescOf firstGenerator = some firstRule)
    (secondIsFlatFormation : flatTypingRuleDescOf secondGenerator = some secondRule) :
    ¬ Conv (.mkGen firstGenerator firstPayload firstChildren)
        (.mkGen secondGenerator secondPayload secondChildren) :=
  fun convertibility =>
    distinct
      (Conv.flatFormationFormerGeneratorEq convertibility firstIsFlatFormation secondIsFlatFormation)

/-- **Concrete non-vacuity: a product type is never a sum type.**  `A × B` is never convertible to `A + B`
(`gen_productCode ≠ gen_sumCode`, `Generator.noConfusion`) — a `by`-free instance of the generic flat theorem
over arbitrary payloads/children. -/
theorem Conv.productCode_not_conv_sumCode {scope : Nat}
    {productPayload : Generator.gen_productCode.payload scope}
    {productChildren : RawTermChildren Generator.gen_productCode.binderShifts scope}
    {sumPayload : Generator.gen_sumCode.payload scope}
    {sumChildren : RawTermChildren Generator.gen_sumCode.binderShifts scope}
    (convertibility :
      Conv (.mkGen .gen_productCode productPayload productChildren)
        (.mkGen .gen_sumCode sumPayload sumChildren)) :
    False :=
  Conv.flatFormationFormersNotConvOfDistinct
    (fun headsEqual => Generator.noConfusion headsEqual)
    flatTypingRuleDescOf_productCode flatTypingRuleDescOf_sumCode convertibility

end FX1Poly.Typed
