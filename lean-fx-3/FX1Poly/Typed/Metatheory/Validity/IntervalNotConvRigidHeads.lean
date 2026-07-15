import FX1Poly.Typed.Engine.Formation.ConvDataCodeInjectivity
import FX1Poly.Core.Rewriting.Confluence.RawConfluence

/-! # FX1Poly/Typed/Metatheory/Validity/IntervalNotConvRigidHeads
    — the interval-non-fibrancy DISCHARGE family: every rigid type-former head is NOT convertible to the interval

The interval becomes a genuine non-fibrant DIMENSION (#1886 / FIBRANCY-AXIS-0).  The validity invariant
`HasTypeUnion.classifierIsType` correspondingly weakens to `UnionClassifierIsPretype = UnionClassifierIsType ∨
UnionClassifierIsDimension`, where `UnionClassifierIsDimension context C := Conv C intervalTypeCell` is the named
hook for the non-fibrant dimensions (interval now; clock / cohesion later).  A site that genuinely needs FIBRANCY
(Π/Σ formation re-typing, the SR closure's reclassification, the binder-row well-formedness) discharges the
`Or.inr` (dimension) branch by proving the classifier in hand is NOT convertible to the interval.

This file ships exactly those discharges — `¬ Conv X intervalTypeCell` for every rigid type-former head X (the
data type codes, the graded-binder codes, the term-indexed codes).  Because `UnionClassifierIsDimension context C`
is DEFINITIONALLY `Conv C intervalTypeCell`, each lemma here IS the `¬ UnionClassifierIsDimension` the consumer
needs (the consumer unfolds the def by `rfl` / `dsimp only`).  The universe-code discharge already ships as
`intervalTypeCell_not_conv_universeCodeCell` (its `Conv.sym` gives `¬ Conv (universeCodeCell …) intervalTypeCell`).

## The two proof shapes (mirroring the shipped `Conv.*_not_universeCode` family)

  * **Leaf heads** (`Bool` / `Nat` / `Unit`): both the code and the interval are step-normal-form leaves, so
    global confluence (`Conv.iff_normalForms_eq_of_confluence`, no SN premise) collapses convertibility to
    syntactic equality — refuted by the distinct head generators (`Generator.noConfusion`).
  * **Shape-stable formers** (`product` / `sum` / `either` / `list` / `option` / `id` / `Π` / `Σ` / `bridge`):
    the former is head-stable under `StepStar` (`StepStar.shapeStable_*General`, every reduct stays
    former-headed), the interval is a normal leaf (`StepStar.eq_of_noStep` collapses its chain), so the shared
    reduct would carry both the former head AND `gen_intervalCode` — `Generator.noConfusion`.

## Zero-axiom verification

`Conv.iff_normalForms_eq_of_confluence` / `StepStar.eq_of_noStep` / `RawTerm.isStepNormalForm_blocks_step` /
`StepStar.shapeStable_*General` / `Generator.noConfusion` / `congrArg` — the exact primitives of the shipped
`Conv.unitTypeCell_not_universeCode` / `Conv.bridgeTypeCell_not_universeCode`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`, `decide`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax

/-! ## Leaf heads -/

/-- **`Bool` is not convertible to the interval.**  Both are step-normal leaves; confluence collapses
convertibility to equality, refuted by distinct head generators. -/
theorem boolTypeCell_not_conv_intervalTypeCell {scope : Nat} :
    ¬ Conv (boolTypeCell : RawTerm scope) intervalTypeCell := by
  intro conv
  have boolNormal : RawTerm.isStepNormalForm (boolTypeCell : RawTerm scope) := rfl
  have intervalNormal : RawTerm.isStepNormalForm (intervalTypeCell : RawTerm scope) := rfl
  have codesEqual : (boolTypeCell : RawTerm scope) = intervalTypeCell :=
    (Conv.iff_normalForms_eq_of_confluence (StepStar.refl _) boolNormal (StepStar.refl _)
      intervalNormal).mp conv
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator codesEqual : Generator.gen_boolCode = Generator.gen_intervalCode)

/-- **`Nat` is not convertible to the interval.** -/
theorem natTypeCell_not_conv_intervalTypeCell {scope : Nat} :
    ¬ Conv (natTypeCell : RawTerm scope) intervalTypeCell := by
  intro conv
  have natNormal : RawTerm.isStepNormalForm (natTypeCell : RawTerm scope) := rfl
  have intervalNormal : RawTerm.isStepNormalForm (intervalTypeCell : RawTerm scope) := rfl
  have codesEqual : (natTypeCell : RawTerm scope) = intervalTypeCell :=
    (Conv.iff_normalForms_eq_of_confluence (StepStar.refl _) natNormal (StepStar.refl _)
      intervalNormal).mp conv
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator codesEqual : Generator.gen_natCode = Generator.gen_intervalCode)

/-- **`Unit` is not convertible to the interval.** -/
theorem unitTypeCell_not_conv_intervalTypeCell {scope : Nat} :
    ¬ Conv (unitTypeCell : RawTerm scope) intervalTypeCell := by
  intro conv
  have unitNormal : RawTerm.isStepNormalForm (unitTypeCell : RawTerm scope) := rfl
  have intervalNormal : RawTerm.isStepNormalForm (intervalTypeCell : RawTerm scope) := rfl
  have codesEqual : (unitTypeCell : RawTerm scope) = intervalTypeCell :=
    (Conv.iff_normalForms_eq_of_confluence (StepStar.refl _) unitNormal (StepStar.refl _)
      intervalNormal).mp conv
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator codesEqual : Generator.gen_unitCode = Generator.gen_intervalCode)

/-- **`Empty` is not convertible to the interval.** -/
theorem emptyTypeCell_not_conv_intervalTypeCell {scope : Nat} :
    ¬ Conv (emptyTypeCell : RawTerm scope) intervalTypeCell := by
  intro conv
  have emptyNormal : RawTerm.isStepNormalForm (emptyTypeCell : RawTerm scope) := rfl
  have intervalNormal : RawTerm.isStepNormalForm (intervalTypeCell : RawTerm scope) := rfl
  have codesEqual : (emptyTypeCell : RawTerm scope) = intervalTypeCell :=
    (Conv.iff_normalForms_eq_of_confluence (StepStar.refl _) emptyNormal (StepStar.refl _)
      intervalNormal).mp conv
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator codesEqual : Generator.gen_emptyCode = Generator.gen_intervalCode)

/-! ## Shape-stable formers — the helper `StepStar interval _ → _ = interval` collapse -/

/-- The interval's `StepStar` chain is reflexive: it is a step-normal leaf, so any chain out of it lands back on
the interval.  The right-chain collapse every shape-stable discharge below shares. -/
theorem stepStar_intervalTypeCell_eq {scope : Nat} {target : RawTerm scope}
    (chain : StepStar (intervalTypeCell : RawTerm scope) target) :
    target = (intervalTypeCell : RawTerm scope) :=
  StepStar.eq_of_noStep
    (fun reduct step => RawTerm.isStepNormalForm_blocks_step
      (rfl : RawTerm.isStepNormalForm (intervalTypeCell : RawTerm scope)) reduct step) chain

/-- **`product A B` is not convertible to the interval.**  `product` is head-stable; the interval is a normal
leaf; the shared reduct carries both heads. -/
theorem productTypeCell_not_conv_intervalTypeCell {scope : Nat} (firstType secondType : RawTerm scope) :
    ¬ Conv (productTypeCell firstType secondType) intervalTypeCell := by
  intro conv
  obtain ⟨commonReduct, leftChain, rightChain⟩ := conv
  obtain ⟨_firstAfter, _secondAfter, leftCommonEq, _, _⟩ :=
    StepStar.shapeStable_productCodeGeneral leftChain firstType secondType rfl
  have rightCommonEq := stepStar_intervalTypeCell_eq rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq : Generator.gen_productCode = Generator.gen_intervalCode)

/-- **`sum A B` is not convertible to the interval.** -/
theorem sumTypeCell_not_conv_intervalTypeCell {scope : Nat} (firstType secondType : RawTerm scope) :
    ¬ Conv (.mkGen .gen_sumCode () (.childCons firstType (.childCons secondType .childNil)) : RawTerm scope)
        intervalTypeCell := by
  intro conv
  obtain ⟨commonReduct, leftChain, rightChain⟩ := conv
  obtain ⟨_firstAfter, _secondAfter, leftCommonEq, _, _⟩ :=
    StepStar.shapeStable_sumCodeGeneral leftChain firstType secondType rfl
  have rightCommonEq := stepStar_intervalTypeCell_eq rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq : Generator.gen_sumCode = Generator.gen_intervalCode)

/-- **`either A B` is not convertible to the interval.** -/
theorem eitherTypeCell_not_conv_intervalTypeCell {scope : Nat} (leftType rightType : RawTerm scope) :
    ¬ Conv (eitherTypeCell leftType rightType) intervalTypeCell := by
  intro conv
  obtain ⟨commonReduct, leftChain, rightChain⟩ := conv
  obtain ⟨_leftAfter, _rightAfter, leftCommonEq, _, _⟩ :=
    StepStar.shapeStable_eitherCodeGeneral leftChain leftType rightType rfl
  have rightCommonEq := stepStar_intervalTypeCell_eq rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq : Generator.gen_eitherCode = Generator.gen_intervalCode)

/-- **`List A` is not convertible to the interval.** -/
theorem listTypeCell_not_conv_intervalTypeCell {scope : Nat} (elementType : RawTerm scope) :
    ¬ Conv (listTypeCell elementType) intervalTypeCell := by
  intro conv
  obtain ⟨commonReduct, leftChain, rightChain⟩ := conv
  obtain ⟨_elementAfter, leftCommonEq, _⟩ :=
    StepStar.shapeStable_listCodeGeneral leftChain elementType rfl
  have rightCommonEq := stepStar_intervalTypeCell_eq rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq : Generator.gen_listCode = Generator.gen_intervalCode)

/-- **`Option A` is not convertible to the interval.** -/
theorem optionTypeCell_not_conv_intervalTypeCell {scope : Nat} (elementType : RawTerm scope) :
    ¬ Conv (optionTypeCell elementType) intervalTypeCell := by
  intro conv
  obtain ⟨commonReduct, leftChain, rightChain⟩ := conv
  obtain ⟨_elementAfter, leftCommonEq, _⟩ :=
    StepStar.shapeStable_optionCodeGeneral leftChain elementType rfl
  have rightCommonEq := stepStar_intervalTypeCell_eq rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq : Generator.gen_optionCode = Generator.gen_intervalCode)

/-- **`Id A l r` is not convertible to the interval.** -/
theorem idTypeCell_not_conv_intervalTypeCell {scope : Nat} (typeCode left right : RawTerm scope) :
    ¬ Conv (idTypeCell typeCode left right) intervalTypeCell := by
  intro conv
  obtain ⟨commonReduct, leftChain, rightChain⟩ := conv
  obtain ⟨_typeAfter, _leftAfter, _rightAfter, leftCommonEq, _, _, _⟩ :=
    StepStar.shapeStable_idCodeGeneral leftChain typeCode left right rfl
  have rightCommonEq := stepStar_intervalTypeCell_eq rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq : Generator.gen_idCode = Generator.gen_intervalCode)

/-- **`Π A B` is not convertible to the interval.**  The graded-binder code; the codomain crosses one binder. -/
theorem piTyCodeCell_not_conv_intervalTypeCell {scope : Nat}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    ¬ Conv (piTyCodeCell domainCode codomainCode) intervalTypeCell := by
  intro conv
  obtain ⟨commonReduct, leftChain, rightChain⟩ := conv
  obtain ⟨_domainAfter, _codomainAfter, leftCommonEq, _, _⟩ :=
    StepStar.shapeStable_piTyCodeGeneral leftChain domainCode codomainCode rfl
  have rightCommonEq := stepStar_intervalTypeCell_eq rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq : Generator.gen_piTyCode = Generator.gen_intervalCode)

/-- **`Σ A B` is not convertible to the interval.** -/
theorem sigmaTyCodeCell_not_conv_intervalTypeCell {scope : Nat}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    ¬ Conv (sigmaTyCodeCell domainCode codomainCode) intervalTypeCell := by
  intro conv
  obtain ⟨commonReduct, leftChain, rightChain⟩ := conv
  obtain ⟨_domainAfter, _codomainAfter, leftCommonEq, _, _⟩ :=
    StepStar.shapeStable_sigmaTyCodeGeneral leftChain domainCode codomainCode rfl
  have rightCommonEq := stepStar_intervalTypeCell_eq rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq : Generator.gen_sigmaTyCode = Generator.gen_intervalCode)

/-- **`Bridge A l r` is not convertible to the interval.**  The term-indexed bridge code — the pathLam output
type — is head-stable; the SR pathApp gate discharges its path classifier through this. -/
theorem bridgeTypeCell_not_conv_intervalTypeCell {scope : Nat} (typeCode left right : RawTerm scope) :
    ¬ Conv (bridgeTypeCell typeCode left right) intervalTypeCell := by
  intro conv
  obtain ⟨commonReduct, leftChain, rightChain⟩ := conv
  obtain ⟨_typeAfter, _leftAfter, _rightAfter, leftCommonEq, _, _, _⟩ :=
    StepStar.shapeStable_bridgeTypeGeneral leftChain typeCode left right rfl
  have rightCommonEq := stepStar_intervalTypeCell_eq rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq : Generator.gen_bridgeCode = Generator.gen_intervalCode)

end FX1Poly.Typed
