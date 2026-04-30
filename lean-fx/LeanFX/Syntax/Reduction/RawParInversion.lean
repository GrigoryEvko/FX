import LeanFX.Syntax.Reduction.RawPar

namespace LeanFX.Syntax

/-! ## Inversion lemmas for `RawStep.par`.

For each `RawTerm` constructor `C`, the lemma `RawStep.par.C_inv`
states: when `RawStep.par (C args) target`, the target is also of
shape `C args'` with appropriate parallel-step relations on the
sub-terms.

These work because `RawStep.par` is indexed only by `scope : Nat`,
not by typed `Ty` indices, so Lean's `cases` tactic can decompose
the inductive without dependent-elimination conflicts.

These lemmas are exactly what `cd_lemma`'s deep cases need: from
"function reduces to a lam-shaped value via the IH" we recover the
lam structure of the IH's target, allowing the deep-rule's
contraction shape to be matched. -/

theorem RawStep.par.lam_inv {scope : Nat} {body : RawTerm (scope + 1)}
    {target : RawTerm scope} (step : RawStep.par (RawTerm.lam body) target) :
    ∃ body', target = RawTerm.lam body' ∧ RawStep.par body body' := by
  cases step with
  | refl _ => exact ⟨body, rfl, RawStep.par.refl _⟩
  | lam pb => exact ⟨_, rfl, pb⟩

theorem RawStep.par.pair_inv {scope : Nat}
    {firstVal secondVal : RawTerm scope} {target : RawTerm scope}
    (step : RawStep.par (RawTerm.pair firstVal secondVal) target) :
    ∃ firstVal' secondVal',
      target = RawTerm.pair firstVal' secondVal' ∧
        RawStep.par firstVal firstVal' ∧
        RawStep.par secondVal secondVal' := by
  cases step with
  | refl _ =>
      exact ⟨firstVal, secondVal, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | pair pf ps => exact ⟨_, _, rfl, pf, ps⟩

theorem RawStep.par.refl_inv {scope : Nat}
    {rawTerm : RawTerm scope} {target : RawTerm scope}
    (step : RawStep.par (RawTerm.refl rawTerm) target) :
    target = RawTerm.refl rawTerm := by
  cases step
  case refl _ => rfl

theorem RawStep.par.boolTrue_inv {scope : Nat}
    {target : RawTerm scope}
    (step : RawStep.par (RawTerm.boolTrue : RawTerm scope) target) :
    target = RawTerm.boolTrue := by
  cases step
  case refl _ => rfl

theorem RawStep.par.boolFalse_inv {scope : Nat}
    {target : RawTerm scope}
    (step : RawStep.par (RawTerm.boolFalse : RawTerm scope) target) :
    target = RawTerm.boolFalse := by
  cases step
  case refl _ => rfl

theorem RawStep.par.natZero_inv {scope : Nat}
    {target : RawTerm scope}
    (step : RawStep.par (RawTerm.natZero : RawTerm scope) target) :
    target = RawTerm.natZero := by
  cases step
  case refl _ => rfl

theorem RawStep.par.natSucc_inv {scope : Nat}
    {predecessor : RawTerm scope} {target : RawTerm scope}
    (step : RawStep.par (RawTerm.natSucc predecessor) target) :
    ∃ predecessor', target = RawTerm.natSucc predecessor' ∧
      RawStep.par predecessor predecessor' := by
  cases step with
  | refl _ => exact ⟨predecessor, rfl, RawStep.par.refl _⟩
  | natSucc pp => exact ⟨_, rfl, pp⟩

theorem RawStep.par.listNil_inv {scope : Nat}
    {target : RawTerm scope}
    (step : RawStep.par (RawTerm.listNil : RawTerm scope) target) :
    target = RawTerm.listNil := by
  cases step
  case refl _ => rfl

theorem RawStep.par.listCons_inv {scope : Nat}
    {head tail : RawTerm scope} {target : RawTerm scope}
    (step : RawStep.par (RawTerm.listCons head tail) target) :
    ∃ head' tail', target = RawTerm.listCons head' tail' ∧
      RawStep.par head head' ∧ RawStep.par tail tail' := by
  cases step with
  | refl _ =>
      exact ⟨head, tail, rfl, RawStep.par.refl _, RawStep.par.refl _⟩
  | listCons ph pt => exact ⟨_, _, rfl, ph, pt⟩

theorem RawStep.par.optionNone_inv {scope : Nat}
    {target : RawTerm scope}
    (step : RawStep.par (RawTerm.optionNone : RawTerm scope) target) :
    target = RawTerm.optionNone := by
  cases step
  case refl _ => rfl

theorem RawStep.par.optionSome_inv {scope : Nat}
    {value : RawTerm scope} {target : RawTerm scope}
    (step : RawStep.par (RawTerm.optionSome value) target) :
    ∃ value', target = RawTerm.optionSome value' ∧
      RawStep.par value value' := by
  cases step with
  | refl _ => exact ⟨value, rfl, RawStep.par.refl _⟩
  | optionSome pv => exact ⟨_, rfl, pv⟩

theorem RawStep.par.eitherInl_inv {scope : Nat}
    {value : RawTerm scope} {target : RawTerm scope}
    (step : RawStep.par (RawTerm.eitherInl value) target) :
    ∃ value', target = RawTerm.eitherInl value' ∧
      RawStep.par value value' := by
  cases step with
  | refl _ => exact ⟨value, rfl, RawStep.par.refl _⟩
  | eitherInl pv => exact ⟨_, rfl, pv⟩

theorem RawStep.par.eitherInr_inv {scope : Nat}
    {value : RawTerm scope} {target : RawTerm scope}
    (step : RawStep.par (RawTerm.eitherInr value) target) :
    ∃ value', target = RawTerm.eitherInr value' ∧
      RawStep.par value value' := by
  cases step with
  | refl _ => exact ⟨value, rfl, RawStep.par.refl _⟩
  | eitherInr pv => exact ⟨_, rfl, pv⟩

end LeanFX.Syntax
