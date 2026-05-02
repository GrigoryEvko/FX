import LeanFX2.Reduction.RawPar

/-! # Reduction/RawParInversion — inversion lemmas for RawStep.par

For each `RawTerm` constructor `C`, the lemma `RawStep.par.C_inv`
states: when `RawStep.par (C args) target`, `target` has the same
shape `C args'` with appropriate parallel-step relations on the
sub-terms (or `target = C args` for nullary canonical ctors).

These work because `RawStep.par` is indexed only by `scope : Nat`
(no Ty indices), so Lean's `cases` tactic decomposes the inductive
without dependent-elimination conflicts.  Per
`feedback_lean_match_arity_axioms.md`, single-Nat-indexed inductives
do NOT trigger propext+Quot.sound on `cases`.

These are exactly what `RawStep.par.cd_lemma`'s deep cases need:
from "subterm reduces to canonical via the IH" we recover the
canonical structure of the IH's target, allowing the deep-rule's
contraction shape to be matched.

## Modal ctors

`modIntro_inv`, `modElim_inv`, `subsume_inv` follow the same pattern
as `optionSome_inv` / `eitherInl_inv` (single subterm cong).  No
`iota` rule applies to modal cases since lean-fx-2's RawStep.par
omits `iotaModal*`; the modality reduction lives in Layer 6.
-/

namespace LeanFX2

/-- `RawStep.par (lam body) target → target = lam body' ∧ par body body'`. -/
theorem RawStep.par.lam_inv {scope : Nat} {body : RawTerm (scope + 1)}
    {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.lam body) target) :
    ∃ bodyTarget, target = RawTerm.lam bodyTarget ∧
      RawStep.par body bodyTarget := by
  cases parallelStep with
  | refl _ => exact ⟨body, rfl, RawStep.par.refl _⟩
  | lam bodyStep => exact ⟨_, rfl, bodyStep⟩

/-- `RawStep.par (pair fv sv) target → target = pair fv' sv' ∧ pars`. -/
theorem RawStep.par.pair_inv {scope : Nat}
    {firstValue secondValue : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.pair firstValue secondValue) target) :
    ∃ firstTarget secondTarget,
      target = RawTerm.pair firstTarget secondTarget ∧
        RawStep.par firstValue firstTarget ∧
        RawStep.par secondValue secondTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨firstValue, secondValue, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | pair firstStep secondStep => exact ⟨_, _, rfl, firstStep, secondStep⟩

/-- `RawStep.par (refl rw) target → target = refl rw' ∧ par rw rw'`.
Note that RawStep.par.reflCong's existence makes this distinct from
`pair_inv` — refl is NOT frozen at the raw level. -/
theorem RawStep.par.refl_inv {scope : Nat}
    {rawWitness : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.refl rawWitness) target) :
    ∃ witnessTarget, target = RawTerm.refl witnessTarget ∧
      RawStep.par rawWitness witnessTarget := by
  cases parallelStep with
  | refl _ => exact ⟨rawWitness, rfl, RawStep.par.refl _⟩
  | reflCong witnessStep => exact ⟨_, rfl, witnessStep⟩

/-- `RawStep.par boolTrue target → target = boolTrue` (canonical). -/
theorem RawStep.par.boolTrue_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.boolTrue : RawTerm scope) target) :
    target = RawTerm.boolTrue := by
  cases parallelStep
  case refl _ => rfl

/-- `RawStep.par boolFalse target → target = boolFalse`. -/
theorem RawStep.par.boolFalse_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.boolFalse : RawTerm scope) target) :
    target = RawTerm.boolFalse := by
  cases parallelStep
  case refl _ => rfl

/-- `RawStep.par natZero target → target = natZero`. -/
theorem RawStep.par.natZero_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.natZero : RawTerm scope) target) :
    target = RawTerm.natZero := by
  cases parallelStep
  case refl _ => rfl

/-- `RawStep.par (natSucc p) target → target = natSucc p' ∧ par p p'`. -/
theorem RawStep.par.natSucc_inv {scope : Nat}
    {predecessor : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.natSucc predecessor) target) :
    ∃ predecessorTarget, target = RawTerm.natSucc predecessorTarget ∧
      RawStep.par predecessor predecessorTarget := by
  cases parallelStep with
  | refl _ => exact ⟨predecessor, rfl, RawStep.par.refl _⟩
  | natSucc predecessorStep => exact ⟨_, rfl, predecessorStep⟩

/-- `RawStep.par listNil target → target = listNil`. -/
theorem RawStep.par.listNil_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.listNil : RawTerm scope) target) :
    target = RawTerm.listNil := by
  cases parallelStep
  case refl _ => rfl

/-- `RawStep.par (listCons h t) target → target = listCons h' t' ∧ pars`. -/
theorem RawStep.par.listCons_inv {scope : Nat}
    {headTerm tailTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.listCons headTerm tailTerm) target) :
    ∃ headTarget tailTarget,
      target = RawTerm.listCons headTarget tailTarget ∧
        RawStep.par headTerm headTarget ∧
        RawStep.par tailTerm tailTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨headTerm, tailTerm, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | listCons headStep tailStep => exact ⟨_, _, rfl, headStep, tailStep⟩

/-- `RawStep.par optionNone target → target = optionNone`. -/
theorem RawStep.par.optionNone_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.optionNone : RawTerm scope) target) :
    target = RawTerm.optionNone := by
  cases parallelStep
  case refl _ => rfl

/-- `RawStep.par (optionSome v) target → target = optionSome v' ∧ par v v'`. -/
theorem RawStep.par.optionSome_inv {scope : Nat}
    {valueTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.optionSome valueTerm) target) :
    ∃ valueTarget, target = RawTerm.optionSome valueTarget ∧
      RawStep.par valueTerm valueTarget := by
  cases parallelStep with
  | refl _ => exact ⟨valueTerm, rfl, RawStep.par.refl _⟩
  | optionSome valueStep => exact ⟨_, rfl, valueStep⟩

/-- `RawStep.par (eitherInl v) target → target = eitherInl v' ∧ par v v'`. -/
theorem RawStep.par.eitherInl_inv {scope : Nat}
    {valueTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.eitherInl valueTerm) target) :
    ∃ valueTarget, target = RawTerm.eitherInl valueTarget ∧
      RawStep.par valueTerm valueTarget := by
  cases parallelStep with
  | refl _ => exact ⟨valueTerm, rfl, RawStep.par.refl _⟩
  | eitherInl valueStep => exact ⟨_, rfl, valueStep⟩

/-- `RawStep.par (eitherInr v) target → target = eitherInr v' ∧ par v v'`. -/
theorem RawStep.par.eitherInr_inv {scope : Nat}
    {valueTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.eitherInr valueTerm) target) :
    ∃ valueTarget, target = RawTerm.eitherInr valueTarget ∧
      RawStep.par valueTerm valueTarget := by
  cases parallelStep with
  | refl _ => exact ⟨valueTerm, rfl, RawStep.par.refl _⟩
  | eitherInr valueStep => exact ⟨_, rfl, valueStep⟩

/-- `RawStep.par (modIntro inner) target → target = modIntro inner' ∧ par`. -/
theorem RawStep.par.modIntro_inv {scope : Nat}
    {innerTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.modIntro innerTerm) target) :
    ∃ innerTarget, target = RawTerm.modIntro innerTarget ∧
      RawStep.par innerTerm innerTarget := by
  cases parallelStep with
  | refl _ => exact ⟨innerTerm, rfl, RawStep.par.refl _⟩
  | modIntro innerStep => exact ⟨_, rfl, innerStep⟩

/-- `RawStep.par (modElim inner) target → target = modElim inner' ∧ par`. -/
theorem RawStep.par.modElim_inv {scope : Nat}
    {innerTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.modElim innerTerm) target) :
    ∃ innerTarget, target = RawTerm.modElim innerTarget ∧
      RawStep.par innerTerm innerTarget := by
  cases parallelStep with
  | refl _ => exact ⟨innerTerm, rfl, RawStep.par.refl _⟩
  | modElim innerStep => exact ⟨_, rfl, innerStep⟩

/-- `RawStep.par (subsume inner) target → target = subsume inner' ∧ par`. -/
theorem RawStep.par.subsume_inv {scope : Nat}
    {innerTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.subsume innerTerm) target) :
    ∃ innerTarget, target = RawTerm.subsume innerTarget ∧
      RawStep.par innerTerm innerTarget := by
  cases parallelStep with
  | refl _ => exact ⟨innerTerm, rfl, RawStep.par.refl _⟩
  | subsume innerStep => exact ⟨_, rfl, innerStep⟩

end LeanFX2
