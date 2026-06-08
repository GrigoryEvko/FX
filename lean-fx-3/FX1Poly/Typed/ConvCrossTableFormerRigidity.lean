import FX1Poly.Typed.ConvFormationFormerRigidity
import FX1Poly.Typed.ConvFlatFormerRigidity
import FX1Poly.Core.ConvNormalForm

/-! # FX1Poly/Typed/ConvCrossTableFormerRigidity — the CROSS-TABLE cross-former `Conv` discrimination,
    completing the data type-code "no confusion".

`ConvFormationFormerRigidity` (CANON-RO-GEN) discriminates two `typingRuleDescOf`-formers (Π / Σ / list /
option); `ConvFlatFormerRigidity` (CANON-RO-FLAT) discriminates two `flatTypingRuleDescOf`-formers (product /
sum / either / arrow / equiv).  Neither covers a former from ONE table against a former from the OTHER.  This
file ships that CROSS-TABLE discrimination — a `typingRuleDescOf`-former is never convertible to a
`flatTypingRuleDescOf`-former — completing the cross-former no-confusion for EVERY pair of distinct data
type-code formers.

## Why this is load-bearing for SN-049 data canonicity

The data-canonicity rule-outs (SN-049: pair / sum / either) need exactly the cross-table case.  For a closed
normal `t : productCode A B`, `closedNormalSubjectHead` pins `t`'s head to `{lam, piTyCode, sigmaTyCode,
universeCode, listCode, optionCode}` — all of which carry a `typingRuleDescOf` classifier (a `lam` is
classified by a `piTyCode`; each former by `universeCode`).  Ruling each out against `productCode` is the
cross-table discrimination `piTyCode ≢ productCode` (etc.) — which neither per-table file provides.

## The construction needs NO table-disjointness helper

The cross-table proof is the SAME head-stability argument, simply using the LEFT former's head-stability
(`StepStar.formationFormerHeadStableGeneral`, keyed on `typingRuleDescOf`) and the RIGHT former's
head-stability (`StepStar.flatFormationFormerHeadStableGeneral`, keyed on `flatTypingRuleDescOf`).  A `Conv`
join forces a shared common reduct headed by BOTH generators, so they are `headGenerator`-equal — refuted by
the PER-INSTANCE distinctness `g1 ≠ g2` (`Generator.noConfusion` on the two concrete generators).  No generic
"the two tables are disjoint" lemma is needed.

## Contents

* `Conv.crossTableFormersNotConvOfDistinct` — distinct (`typingRuleDescOf`-former, `flatTypingRuleDescOf`-former)
  pairs are never convertible.
* `Conv.piTyCode_not_conv_productCode` — `Π … ≢ A × B` (rules out a `lam` subject at a product classifier).
* `Conv.sigmaTyCode_not_conv_eitherCode` — `Σ … ≢ Either A B` (a second concrete rule-out).

## Zero-axiom

Both shipped head-stability lemmas + the `Conv`/`Join` unpack + `congrArg RawTerm.headGenerator` +
`Generator.noConfusion`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Cross-table discrimination.**  A distinct (`typingRuleDescOf`-former, `flatTypingRuleDescOf`-former) pair
is never convertible: the left side is head-stable via `formationFormerHeadStableGeneral`, the right side via
`flatFormationFormerHeadStableGeneral`, so a shared reduct carries both generators — refuted by the
per-instance distinctness `firstGenerator ≠ secondGenerator`. -/
theorem Conv.crossTableFormersNotConvOfDistinct {scope : Nat}
    {firstGenerator secondGenerator : Generator}
    {firstPayload : firstGenerator.payload scope}
    {firstChildren : RawTermChildren firstGenerator.binderShifts scope}
    {secondPayload : secondGenerator.payload scope}
    {secondChildren : RawTermChildren secondGenerator.binderShifts scope}
    {firstRule secondRule : TypingRuleDesc}
    (distinct : firstGenerator ≠ secondGenerator)
    (firstIsFormation : typingRuleDescOf firstGenerator = some firstRule)
    (secondIsFlatFormation : flatTypingRuleDescOf secondGenerator = some secondRule) :
    ¬ Conv (.mkGen firstGenerator firstPayload firstChildren)
        (.mkGen secondGenerator secondPayload secondChildren) := by
  intro convertibility
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨_firstChildrenAfter, leftEq⟩ :=
    StepStar.formationFormerHeadStableGeneral leftChain firstGenerator firstPayload firstChildren
      firstRule rfl firstIsFormation
  obtain ⟨_secondChildrenAfter, rightEq⟩ :=
    StepStar.flatFormationFormerHeadStableGeneral rightChain secondGenerator secondPayload secondChildren
      secondRule rfl secondIsFlatFormation
  rw [leftEq] at rightEq
  exact distinct (congrArg RawTerm.headGenerator rightEq)

/-- **`Π … ≢ A × B`.**  A dependent function type is never convertible to a product — the cross-table rule-out
that kills a `lam` subject (classified by a Π-code) at a `productCode` classifier in pair canonicity (SN-049).
A `by`-free instance over arbitrary payloads/children. -/
theorem Conv.piTyCode_not_conv_productCode {scope : Nat}
    {piPayload : Generator.gen_piTyCode.payload scope}
    {piChildren : RawTermChildren Generator.gen_piTyCode.binderShifts scope}
    {productPayload : Generator.gen_productCode.payload scope}
    {productChildren : RawTermChildren Generator.gen_productCode.binderShifts scope}
    (convertibility :
      Conv (.mkGen .gen_piTyCode piPayload piChildren)
        (.mkGen .gen_productCode productPayload productChildren)) :
    False :=
  Conv.crossTableFormersNotConvOfDistinct
    (fun headsEqual => Generator.noConfusion headsEqual)
    typingRuleDescOf_piTyCode flatTypingRuleDescOf_productCode convertibility

/-- **`Σ … ≢ Either A B`.**  A dependent pair type is never convertible to a coproduct — a second concrete
cross-table rule-out. -/
theorem Conv.sigmaTyCode_not_conv_eitherCode {scope : Nat}
    {sigmaPayload : Generator.gen_sigmaTyCode.payload scope}
    {sigmaChildren : RawTermChildren Generator.gen_sigmaTyCode.binderShifts scope}
    {eitherPayload : Generator.gen_eitherCode.payload scope}
    {eitherChildren : RawTermChildren Generator.gen_eitherCode.binderShifts scope}
    (convertibility :
      Conv (.mkGen .gen_sigmaTyCode sigmaPayload sigmaChildren)
        (.mkGen .gen_eitherCode eitherPayload eitherChildren)) :
    False :=
  Conv.crossTableFormersNotConvOfDistinct
    (fun headsEqual => Generator.noConfusion headsEqual)
    typingRuleDescOf_sigmaTyCode flatTypingRuleDescOf_eitherCode convertibility

end FX1Poly.Typed
