import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Typed.CellConstructors
import FX1Poly.Core.BoolCanonicalFormsCandidate

/-! # FX1Poly/Typed/ConvBoolCodeRigidity — cross-former `Conv` rigidity for the bool type-code
    (the bool-canonicity RULE-OUT substrate).

The companion to the shipped same-former injectivity (`ConvFlatCodeInjectivity` / `ConvDataCodeInjectivity`)
and the Π/Σ/universe rigidity (`ConvCodeInjectivity.lean`): a `boolTypeCell` is never convertible to a
type-FORMER classifier (`piTyCode` / `sigmaTyCode` / `universeCode`).  These are precisely the
discriminations the bool-canonicity rule-out (CANON-1, the link-4 gap) consumes.

## Why these are the CANON-1 rule-outs

`HasTypeDescPi.closedNormalSubjectHead` (GrownCanonicalForms) pins a closed normal subject's head to one of
`{lam, piTyCode, sigmaTyCode, universeCode, listCode, optionCode}`.  For a closed normal `t : boolCode`,
uniqueness of typing forces `t`'s classifier (`boolCode`) convertible to the classifier each candidate head
WOULD carry: `lam` is classified by a `piTyCode` (a Π-type); each type-former (`piTyCode` / `sigmaTyCode` /
`universeCode` / `listCode` / `optionCode`) is classified by `universeCode`.  Each such convertibility is
refuted here (`boolCode ≢ piTyCode` rules out `lam`; `boolCode ≢ universeCode` rules out every type-former),
leaving exactly the data constructors — which the data-intro judgment types and `subjectIsBoolConstructor`
pins to `boolTrue` / `boolFalse`.

## The SN-free mechanism (reused from `ConvCodeInjectivity`)

`boolTypeCell = mkGen gen_boolCode () childNil` is a no-step LEAF (`isStepNormalForm` by `rfl`, childless,
non-redex head), so a `Conv` chain out of it pins its reduct to itself (`StepStar.eq_of_noStep` via
`RawTerm.isStepNormalForm_blocks_step`).  The dependent formers `piTyCode` / `sigmaTyCode` are head-stable
(`StepStar.shapeStable_piTyCode` / `_sigmaTyCode`) and `universeCode` is itself a no-step leaf
(`StepStar.noStep_universeCode`).  A shared `Conv` reduct therefore carries BOTH heads — refuted by
`Generator.noConfusion` on the head-generator projection.  No confluence, no strong normalization — the same
head-stability route as the Π/Σ rigidity.

## Zero-axiom

`StepStar.eq_of_noStep` + `RawTerm.isStepNormalForm_blocks_step` (`rfl` normality) + the shipped
`StepStar.shapeStable_*` / `noStep_universeCode` + `Generator.noConfusion`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **`boolCode` is never convertible to a Π-code.**  Rules out a `lam` subject in bool canonicity (its
classifier is a `piTyCode`).  `boolTypeCell` is a no-step leaf, `piTyCode` is head-stable; a shared reduct
would carry both `gen_boolCode` and `gen_piTyCode` — `Generator.noConfusion`. -/
theorem Conv.boolTypeCell_not_piTyCode {scope : Nat}
    {piDomain : RawTerm scope} {piCodomain : RawTerm (scope + 1)}
    (convertibility : Conv (boolTypeCell : RawTerm scope) (piTyCodeCell piDomain piCodomain)) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  have leftCommonEq :=
    StepStar.eq_of_noStep
      (fun reduct step =>
        RawTerm.isStepNormalForm_blocks_step
          (rfl : RawTerm.isStepNormalForm (boolTypeCell : RawTerm scope)) reduct step)
      leftChain
  obtain ⟨_, _, rightCommonEq, _, _⟩ := StepStar.shapeStable_piTyCode rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq :
      Generator.gen_boolCode = Generator.gen_piTyCode)

/-- **`boolCode` is never convertible to a Σ-code** — the Σ dual of `boolTypeCell_not_piTyCode`. -/
theorem Conv.boolTypeCell_not_sigmaTyCode {scope : Nat}
    {sigmaDomain : RawTerm scope} {sigmaCodomain : RawTerm (scope + 1)}
    (convertibility :
      Conv (boolTypeCell : RawTerm scope) (sigmaTyCodeCell sigmaDomain sigmaCodomain)) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  have leftCommonEq :=
    StepStar.eq_of_noStep
      (fun reduct step =>
        RawTerm.isStepNormalForm_blocks_step
          (rfl : RawTerm.isStepNormalForm (boolTypeCell : RawTerm scope)) reduct step)
      leftChain
  obtain ⟨_, _, rightCommonEq, _, _⟩ := StepStar.shapeStable_sigmaTyCode rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq :
      Generator.gen_boolCode = Generator.gen_sigmaTyCode)

/-- **`boolCode` is never convertible to a universe code.**  Rules out every type-former subject in bool
canonicity (their classifier is `universeCode`).  Both `boolTypeCell` and `universeCodeCell` are no-step
leaves, so a shared reduct equals both — `Generator.noConfusion` on `gen_boolCode` vs `gen_universeCode`. -/
theorem Conv.boolTypeCell_not_universeCode {scope : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (convertibility : Conv (boolTypeCell : RawTerm scope) (universeCodeCell levelExpr flag)) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  have leftCommonEq :=
    StepStar.eq_of_noStep
      (fun reduct step =>
        RawTerm.isStepNormalForm_blocks_step
          (rfl : RawTerm.isStepNormalForm (boolTypeCell : RawTerm scope)) reduct step)
      leftChain
  have rightCommonEq :=
    StepStar.eq_of_noStep
      (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step) rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq :
      Generator.gen_boolCode = Generator.gen_universeCode)

end FX1Poly.Typed
