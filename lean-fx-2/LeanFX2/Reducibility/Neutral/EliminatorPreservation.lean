import LeanFX2.Reducibility.Neutral.NeutralCore

/-! # LeanFX2.Reducibility.Neutral.EliminatorPreservation

Preservation of `RawTerm.IsNeutral` under one raw parallel step
for the Π / Σ / ι-eliminator family: `var`, `app`, `fst`, `snd`,
`boolElim`, `natElim`, `natRec`, `listElim`, `optionMatch`,
`eitherMatch`.  Each arm dispatches on the par step and
discharges the redex-firing arms via the appropriate `not_<ctor>`
from `NeutralCore`.

## Root status

Layer 3 metatheory leaf.  Second slice of `Neutral`. -/

namespace LeanFX2


/-! ### K12.20.U2 neutral preservation under raw parallel development

These higher-order one-step preservation lemmas are the local shape
facts needed by compound CR3.  Each lemma assumes preservation for the
principal neutral subterm and proves preservation for one eliminator
wrapper.  Keeping the lemmas higher-order mirrors the `varShape` and
`step_preserves` architecture: the later global CR3/par-preservation
dispatcher supplies the recursive hook, while these atoms discharge the
constructor-specific beta/iota-impossible cases exactly once.
-/

/-- A variable can only parallel-develop to itself, so neutrality is
preserved by one raw parallel step from a variable. -/
theorem RawTerm.IsNeutral.var_par_preserves {scope : Nat}
    {position : Fin scope} {targetRaw : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.var position) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  have targetEq : targetRaw = RawTerm.var position :=
    RawStep.par.var_inv parallelStep
  subst targetEq
  exact RawTerm.IsNeutral.var position

/-- Neutrality is preserved by one raw parallel step from a neutral
application, assuming preservation for the function head. -/
theorem RawTerm.IsNeutral.app_par_preserves {scope : Nat}
    {functionRaw argumentRaw targetRaw : RawTerm scope}
    (functionParPreserves :
      ∀ {functionTarget : RawTerm scope},
        RawStep.par functionRaw functionTarget →
        RawTerm.IsNeutral functionTarget)
    (parallelStep :
      RawStep.par (RawTerm.app functionRaw argumentRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.app_inv parallelStep with
    ⟨functionTarget, argumentTarget, targetEq,
      functionStep, _argumentStep⟩
    | ⟨bodyTarget, _argumentTarget, _targetEq,
        functionStep, _argumentStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.app (functionParPreserves functionStep)
  · exact (RawTerm.IsNeutral.not_lam
      (functionParPreserves functionStep) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `fst` of a
neutral pair scrutinee. -/
theorem RawTerm.IsNeutral.fst_par_preserves {scope : Nat}
    {pairRaw targetRaw : RawTerm scope}
    (pairParPreserves :
      ∀ {pairTarget : RawTerm scope},
        RawStep.par pairRaw pairTarget →
        RawTerm.IsNeutral pairTarget)
    (parallelStep : RawStep.par (RawTerm.fst pairRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.fst_inv parallelStep with
    ⟨pairTarget, targetEq, pairStep⟩
    | ⟨firstTarget, secondTarget, _targetEq, pairStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.fst (pairParPreserves pairStep)
  · exact (RawTerm.IsNeutral.not_pair
      (pairParPreserves pairStep)
      (firstRaw := firstTarget) (secondRaw := secondTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `snd` of a
neutral pair scrutinee. -/
theorem RawTerm.IsNeutral.snd_par_preserves {scope : Nat}
    {pairRaw targetRaw : RawTerm scope}
    (pairParPreserves :
      ∀ {pairTarget : RawTerm scope},
        RawStep.par pairRaw pairTarget →
        RawTerm.IsNeutral pairTarget)
    (parallelStep : RawStep.par (RawTerm.snd pairRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.snd_inv parallelStep with
    ⟨pairTarget, targetEq, pairStep⟩
    | ⟨firstTarget, secondTarget, _targetEq, pairStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.snd (pairParPreserves pairStep)
  · exact (RawTerm.IsNeutral.not_pair
      (pairParPreserves pairStep)
      (firstRaw := firstTarget) (secondRaw := secondTarget) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `boolElim`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.boolElim_par_preserves {scope : Nat}
    {scrutineeRaw thenRaw elseRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.boolElim scrutineeRaw thenRaw elseRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.boolElim_inv parallelStep with
    ⟨scrutineeTarget, thenTarget, elseTarget, targetEq,
      scrutineeStep, _thenStep, _elseStep⟩
    | ⟨_thenTarget, _targetEq, scrutineeStep, _thenStep⟩
    | ⟨_elseTarget, _targetEq, scrutineeStep, _elseStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.boolElim
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_boolTrue
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_boolFalse
      (scrutineeParPreserves scrutineeStep) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `natElim`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.natElim_par_preserves {scope : Nat}
    {scrutineeRaw zeroRaw succRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.natElim scrutineeRaw zeroRaw succRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.natElim_inv parallelStep with
    ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
      scrutineeStep, _zeroStep, _succStep⟩
    | ⟨_zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
    | ⟨predecessorRaw, _succTarget, _targetEq,
        scrutineeStep, _succStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.natElim
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_natZero
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_natSucc
      (scrutineeParPreserves scrutineeStep)
      (predecessorRaw := predecessorRaw) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `natRec`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.natRec_par_preserves {scope : Nat}
    {scrutineeRaw zeroRaw succRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.natRec scrutineeRaw zeroRaw succRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.natRec_inv parallelStep with
    ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
      scrutineeStep, _zeroStep, _succStep⟩
    | ⟨_zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
    | ⟨predecessorRaw, _zeroTarget, _succTarget, _targetEq,
        scrutineeStep, _zeroStep, _succStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.natRec
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_natZero
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_natSucc
      (scrutineeParPreserves scrutineeStep)
      (predecessorRaw := predecessorRaw) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `listElim`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.listElim_par_preserves {scope : Nat}
    {scrutineeRaw nilRaw consRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.listElim scrutineeRaw nilRaw consRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.listElim_inv parallelStep with
    ⟨scrutineeTarget, nilTarget, consTarget, targetEq,
      scrutineeStep, _nilStep, _consStep⟩
    | ⟨_nilTarget, _targetEq, scrutineeStep, _nilStep⟩
    | ⟨headRaw, tailRaw, _consTarget, _targetEq,
        scrutineeStep, _consStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.listElim
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_listNil
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_listCons
      (scrutineeParPreserves scrutineeStep)
      (headRaw := headRaw) (tailRaw := tailRaw) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `optionMatch`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.optionMatch_par_preserves {scope : Nat}
    {scrutineeRaw noneRaw someRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.optionMatch scrutineeRaw noneRaw someRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.optionMatch_inv parallelStep with
    ⟨scrutineeTarget, noneTarget, someTarget, targetEq,
      scrutineeStep, _noneStep, _someStep⟩
    | ⟨_noneTarget, _targetEq, scrutineeStep, _noneStep⟩
    | ⟨valueRaw, _someTarget, _targetEq, scrutineeStep, _someStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.optionMatch
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_optionNone
      (scrutineeParPreserves scrutineeStep) rfl).elim
  · exact (RawTerm.IsNeutral.not_optionSome
      (scrutineeParPreserves scrutineeStep)
      (valueRaw := valueRaw) rfl).elim

/-- Neutrality is preserved by one raw parallel step from `eitherMatch`
with a neutral scrutinee. -/
theorem RawTerm.IsNeutral.eitherMatch_par_preserves {scope : Nat}
    {scrutineeRaw leftRaw rightRaw targetRaw : RawTerm scope}
    (scrutineeParPreserves :
      ∀ {scrutineeTarget : RawTerm scope},
        RawStep.par scrutineeRaw scrutineeTarget →
        RawTerm.IsNeutral scrutineeTarget)
    (parallelStep :
      RawStep.par
        (RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw) targetRaw) :
    RawTerm.IsNeutral targetRaw := by
  rcases RawStep.par.eitherMatch_inv parallelStep with
    ⟨scrutineeTarget, leftTarget, rightTarget, targetEq,
      scrutineeStep, _leftStep, _rightStep⟩
    | ⟨valueRaw, _leftTarget, _targetEq,
        scrutineeStep, _leftStep⟩
    | ⟨valueRaw, _rightTarget, _targetEq,
        scrutineeStep, _rightStep⟩
  · subst targetEq
    exact RawTerm.IsNeutral.eitherMatch
      (scrutineeParPreserves scrutineeStep)
  · exact (RawTerm.IsNeutral.not_eitherInl
      (scrutineeParPreserves scrutineeStep)
      (valueRaw := valueRaw) rfl).elim
  · exact (RawTerm.IsNeutral.not_eitherInr
      (scrutineeParPreserves scrutineeStep)
      (valueRaw := valueRaw) rfl).elim

end LeanFX2
