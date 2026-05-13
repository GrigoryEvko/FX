import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParRename

/-! # LeanFX2.Reduction.RawParInversion.AtomicCtors

Inversion lemmas for `RawStep.par` on atomic / structural-only ctors:
binders (`lam`), variables, pairs, identity refl, and the closed
canonical heads `unit`, `boolTrue`, `boolFalse`, `natZero`, `listNil`,
`optionNone`, plus their single-subterm cong siblings (`natSucc`,
`listCons`, `optionSome`, `eitherInl`, `eitherInr`).

None of these ctors are eliminator parents — they fire only `refl`
plus a structural cong rule.

## Root status

Layer 2 raw parallel-step inversion helper.  Zero axioms. -/

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
  | funextReflCong applyStep =>
      exact ⟨_, rfl, RawStep.par.reflCong applyStep⟩
  | funextReflAtIdCong applyStep =>
      exact ⟨_, rfl, RawStep.par.reflCong applyStep⟩
  | funextIntroHetCong applyAStep =>
      exact ⟨_, rfl, RawStep.par.reflCong applyAStep⟩

/-- `RawStep.par (RawTerm.var position) target → target = RawTerm.var position`.

`RawStep.par` has no constructor that takes a variable as input — the
only step from a variable is `refl`.  Hence the inversion forces the
target to be the same variable. -/
theorem RawStep.par.var_inv {scope : Nat} {position : Fin scope}
    {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.var position) target) :
    target = RawTerm.var position := by
  cases parallelStep
  case refl _ => rfl

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

/-- `RawStep.par unit target → target = unit` (canonical).

`RawTerm.unit` has no β/ι rules (it's a closed canonical head with
no eliminator chain firing).  Hence the only `RawStep.par` from
`unit` is `refl`. -/
theorem RawStep.par.unit_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.unit : RawTerm scope) target) :
    target = RawTerm.unit := by
  cases parallelStep
  case refl _ => rfl

/-! ### Why no reverse direction `RawStep.par source unit → source = unit`?

The reverse direction is FALSE in general.  Counterexample: take
`body = RawTerm.unit : RawTerm (scope + 1)` (a constant body that
ignores its bound variable) and any `argument : RawTerm scope`.
Then `body.subst (singleton argument) = RawTerm.unit` reduces
`RawTerm.app (RawTerm.lam body) argument` to `RawTerm.unit` via
`RawStep.par.betaApp`.  So `RawStep.par sourceA unit` with sourceA =
`(λ. unit) argument` (NOT `unit`).

Hence `RawStep.par.unit_target_inv` does NOT exist as a theorem.
The forward direction `unit_inv` (from `unit` source to `unit`
target) holds because no β/ι rule has `unit` as a SOURCE — `unit`
has no eliminator that chains through it. -/

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

end LeanFX2
