import FX1Poly.Core.Normalize
import FX1Poly.Core.StepRenameReflectAssembly
import FX1Poly.Tier0.ContextOmega.ModalLock

/-! # Tier0/ContextOmega/MultimodalNormalization — Gratzer multimodal NbE over the modal base (context-12)

**Normalization for multimodal type theory** (Gratzer, "Normalization for Multimodal Type Theory",
arXiv 2301.11842) decides definitional equality by NORMALIZATION-BY-EVALUATION: evaluate a term into a
presheaf model over the renaming/context base, then reify (quote) back to a normal form.  Two terms are
convertible iff their normal forms coincide, so conversion is decidable.  The MULTIMODAL refinement runs
this construction under the modal LOCKS (context-4's `dimensionLock`): the locks are interpreted by
reindexing in the presheaf model, and normalization must respect that reindexing — the normal forms form a
PRESHEAF over the modal base (stable under the lock's reindexing).

On the FX modal base `fxBaseSubstCategory` this is heavily shipped: `Core/Normalize.lean` ships the NbE
normalizer `RawTerm.normalize` (iterate `reduceOnce` along an accessibility witness, halting at a normal
form), the NbE characterization `Conv.iff_normalize_eq_of_isStronglyNormalizing` (sound + complete:
conversion IS normal-form equality on the strongly-normalizing fragment), and the decision procedure
`Conv.decidableOfStronglyNormalizing`.  Over the modal base the normalizer is moreover TOTAL on well-typed
terms — SN-043 (`HasTypeDescPi.closedStronglyNormalizing`) supplies the accessibility witness, so
`HasTypeDescPi.normalForm` (the typed normalizer) needs no hand-supplied termination.  This module exhibits
the NbE construction as living over the CONTEXT ω-category and proves the genuinely-new MULTIMODAL content
zero-axiom: the normal forms are a presheaf over the modal base.

## What is built

  * ★ `normalFormsStableUnderReindexing` — the genuinely-new modal lemma: a step-normal form stays a
    step-normal form after ANY reindexing `rename rho` (the renaming/context-base action).  Proved via
    `Step.reflectRename` (renaming reflects `Step`): a step out of the renamed term reflects to a step out
    of the original, contradicting its normality.  So the NbE normal forms form a PRESHEAF over the modal
    base — exactly Gratzer's modal-stability of normalization.
  * `dimensionLockObjectActionIsScopeSuccessor` — the dimension lock (context-4) shifts the object index by
    one (`◐ : scope ↦ scope + 1`), which is exactly the codomain scope of term weakening: the lock's base
    reindexing IS weakening.
  * `normalFormStableUnderDimensionLock` — the lock's-reindexing instance: a normal form stays normal under
    term weakening (`RawTerm.weaken`), the dimension lock `◐`'s action on the base.
  * `multimodalNormalFormIsReachedAndNormal` — the Gratzer normalization FUNCTION: every
    strongly-normalizing term reduces to `RawTerm.normalize`'s output, which is structurally normal.
  * `multimodalNormalizationSoundComplete` — the NbE characterization (Gratzer's soundness + completeness):
    two SN terms are convertible IFF their normal forms coincide.
  * `conversionDecidableOverModalBase` — the Gratzer payoff: conversion is decidable on the SN fragment
    (normalize each side, compare).
  * ★ `multimodalNormalizationCore` — the headline: the normalizer reaches a normal form, it is a complete
    conversion invariant, and the normal forms are stable under the modal lock's reindexing.

## Honest boundary (recorded, not faked)

The FULL Gratzer NbE construction builds the whole presheaf/gluing NORMALIZATION MODEL (the renaming-indexed
presheaf of values, the modal locks interpreted by reindexing) and proves the normalization function by the
glued model's induction — the QIIT/whole-model recursor over all of syntax, which needs `funext` (the same
boundary as context-3..11: comparing whole value families at every context).  The full presheaf-naturality
`normalize ∘ rename = rename ∘ normalize` (the `Normalizer.normalize_renaming_commute` contract field) needs
`reduceOnce`-renaming-commutation plus accessibility-irrelevance, also off the zero-axiom path for the
`Acc`-recursive normalizer.  What IS zero-axiom is the OPERATIONAL core: the normalizer EXISTS and reaches a
normal form (on the SN fragment, total on well-typed terms via SN-043), is sound + complete for conversion,
decides conversion, and its normal forms are a PRESHEAF over the modal base (stable under reindexing).

## Zero-axiom verification

`normalFormsStableUnderReindexing` is the one new proof: `reduceOnce_eq_none_iff_isStepNormalForm` +
`Step.reflectRename` + `isStepNormalForm_blocks_step` (a renamed step reflects to a source step, refuted by
normality).  The recognitions cite the shipped `RawTerm.normalize_reducesTo` / `_isStepNormalForm` /
`Conv.iff_normalize_eq_of_isStronglyNormalizing` / `Conv.decidableOfStronglyNormalizing`; the lock pin is
`rfl`.  No `funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Core FX1Poly.Tier0.Syntax

/-! ## The genuinely-new modal lemma: normal forms are a presheaf over the modal base -/

/-- ★ **NbE normal forms are stable under the modal base's reindexing.**  A step-normal form stays a
step-normal form after ANY reindexing `rename rho` — so the NbE normal forms form a PRESHEAF over the
renaming/context base, exactly Gratzer's modal-stability of normalization.  Proof: if the renamed term
`rename rho term` had a reduction step, `Step.reflectRename` reflects it to a step out of `term`,
contradicting `term`'s normality (`isStepNormalForm_blocks_step`); so `reduceOnce (rename rho term) = none`,
i.e. the renamed term is normal. -/
theorem normalFormsStableUnderReindexing {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {term : RawTerm sourceScope} (isNF : RawTerm.isStepNormalForm term) :
    RawTerm.isStepNormalForm (RawTerm.rename rho term) := by
  apply RawTerm.reduceOnce_eq_none_iff_isStepNormalForm.mp
  cases hReduce : RawTerm.reduceOnce (RawTerm.rename rho term) with
  | none => rfl
  | some reduct =>
      obtain ⟨sourceReduct, sourceStep, _renameEq⟩ :=
        Step.reflectRename rho (RawTerm.reduceOnce_sound hReduce)
      exact absurd sourceStep (RawTerm.isStepNormalForm_blocks_step isNF sourceReduct)

/-! ## Tying it to the dimension lock (context-4) -/

/-- The dimension lock's object action shifts the index by one (`◐ : scope ↦ scope + 1`).  This is exactly
the codomain scope of term weakening `RawTerm.weaken : RawTerm scope → RawTerm (scope + 1)`, so the lock's
base reindexing IS weakening — the bridge that makes `normalFormStableUnderDimensionLock` an instance of
`normalFormsStableUnderReindexing`. -/
theorem dimensionLockObjectActionIsScopeSuccessor (scope : Nat) :
    dimensionLock.objectMap scope = scope + 1 := rfl

/-- **Normal forms are stable under the dimension lock's reindexing.**  A step-normal form stays normal
under term weakening `RawTerm.weaken` — the context-4 lock `◐`'s action on the base (it reindexes a type
in `Γ` to a type in `Γ.A` by weakening).  The lock-specific instance of `normalFormsStableUnderReindexing`
at `RawRenaming.weaken`. -/
theorem normalFormStableUnderDimensionLock {scope : Nat}
    {term : RawTerm scope} (isNF : RawTerm.isStepNormalForm term) :
    RawTerm.isStepNormalForm (RawTerm.weaken term) := by
  rw [RawTerm.weaken_eq_rename term]
  exact normalFormsStableUnderReindexing RawRenaming.weaken isNF

/-! ## Recognition: the shipped NbE normalizer is the Gratzer normalization function -/

/-- **The Gratzer normalization function over the modal base.**  Every strongly-normalizing term reduces
(by a `StepStar` chain) to `RawTerm.normalize`'s output, which is structurally normal: the NbE normalizer
computes a normal form.  Over the modal base this is TOTAL on well-typed terms — SN-043 supplies the
accessibility witness (`HasTypeDescPi.normalForm`).  Shipped `RawTerm.normalize_reducesTo` /
`_isStepNormalForm`. -/
theorem multimodalNormalFormIsReachedAndNormal {scope : Nat} (term : RawTerm scope)
    (terminates : StepStar.IsStronglyNormalizing term) :
    StepStar term (RawTerm.normalize term terminates) ∧
      RawTerm.isStepNormalForm (RawTerm.normalize term terminates) :=
  ⟨RawTerm.normalize_reducesTo term terminates,
   RawTerm.normalize_isStepNormalForm term terminates⟩

/-- **NbE soundness + completeness (Gratzer's normalization characterization).**  Two strongly-normalizing
terms are convertible IFF their normal forms coincide — the normal form is a COMPLETE conversion invariant.
Shipped `Conv.iff_normalize_eq_of_isStronglyNormalizing`. -/
theorem multimodalNormalizationSoundComplete {scope : Nat}
    {leftTerm rightTerm : RawTerm scope}
    (leftTerminates : StepStar.IsStronglyNormalizing leftTerm)
    (rightTerminates : StepStar.IsStronglyNormalizing rightTerm) :
    Conv leftTerm rightTerm ↔
      RawTerm.normalize leftTerm leftTerminates = RawTerm.normalize rightTerm rightTerminates :=
  Conv.iff_normalize_eq_of_isStronglyNormalizing leftTerminates rightTerminates

/-- **The Gratzer payoff: conversion is decidable over the modal base.**  On the strongly-normalizing
fragment (every well-typed term, by SN-043) conversion is decidable — normalize each side and compare the
normal forms.  Shipped `Conv.decidableOfStronglyNormalizing`. -/
def conversionDecidableOverModalBase {scope : Nat} {leftTerm rightTerm : RawTerm scope}
    (leftTerminates : StepStar.IsStronglyNormalizing leftTerm)
    (rightTerminates : StepStar.IsStronglyNormalizing rightTerm) :
    Decidable (Conv leftTerm rightTerm) :=
  Conv.decidableOfStronglyNormalizing leftTerminates rightTerminates

/-! ## The headline -/

/-- ★ **Gratzer multimodal NbE over the modal base, operational core.**  For two strongly-normalizing terms
and any reindexing `rho` with a normal form `normalTerm`: (a) the NbE normalizer REACHES a normal form
(`leftTerm` reduces to `RawTerm.normalize leftTerm`, which is structurally normal); (b) the NbE
characterization holds — conversion IS normal-form equality (sound + complete); and (c) the normal forms are
STABLE under the modal base's reindexing (`isStepNormalForm (rename rho normalTerm)`), i.e. they form a
presheaf over the modal base.  With `conversionDecidableOverModalBase` (the decision procedure) this is the
operational heart of Gratzer's multimodal normalization.  (The full presheaf-NbE-model recursor + the
normalize/rename commutation are the recorded funext boundary.) -/
theorem multimodalNormalizationCore {scope : Nat}
    (leftTerm rightTerm : RawTerm scope)
    (leftTerminates : StepStar.IsStronglyNormalizing leftTerm)
    (rightTerminates : StepStar.IsStronglyNormalizing rightTerm)
    {sourceScope targetScope : Nat} (rho : RawRenaming sourceScope targetScope)
    {normalTerm : RawTerm sourceScope} (normalTermIsNF : RawTerm.isStepNormalForm normalTerm) :
    StepStar leftTerm (RawTerm.normalize leftTerm leftTerminates) ∧
    RawTerm.isStepNormalForm (RawTerm.normalize leftTerm leftTerminates) ∧
    (Conv leftTerm rightTerm ↔
      RawTerm.normalize leftTerm leftTerminates = RawTerm.normalize rightTerm rightTerminates) ∧
    RawTerm.isStepNormalForm (RawTerm.rename rho normalTerm) :=
  ⟨RawTerm.normalize_reducesTo leftTerm leftTerminates,
   RawTerm.normalize_isStepNormalForm leftTerm leftTerminates,
   Conv.iff_normalize_eq_of_isStronglyNormalizing leftTerminates rightTerminates,
   normalFormsStableUnderReindexing rho normalTermIsNF⟩

end FX1Poly.Tier0.ContextOmega
