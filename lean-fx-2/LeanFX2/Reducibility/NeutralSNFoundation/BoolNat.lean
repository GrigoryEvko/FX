import LeanFX2.Reducibility.SNHelpers
import LeanFX2.Reducibility.Neutral

/-! # LeanFX2.Reducibility.NeutralSNFoundation.BoolNat

Boolean / natural-number recursor SN preservation.  Covers
`boolElim_var` / `boolElim_isStronglyNormalizing`,
`natElim_var_isStronglyNormalizing`, and
`natRec_var_isStronglyNormalizing`.

## Root status

Layer 3 metatheory leaf.  Second slice of NeutralSNFoundation. -/

namespace LeanFX2

/-- **K12.20.AU neutral boolElim SN preservation**.  `RawTerm.boolElim
(var pos) thenBranch elseBranch` is SN when both branches are SN.

First ternary neutral-head SN helper.  boolElim has three subterms
plus two ι rules (`iotaBoolElimTrue` / `False` for true/false
scrutinees).  Variable scrutinee blocks both ι rules via `var_inv`
(var doesn't par-reduce to `boolTrue` or `boolFalse`).  Cong arm
has all three subterms moving in parallel; with the scrutinee
rigid, the effective movement is binary on (thenBranch, elseBranch)
— nested induction like `pair_isStronglyNormalizing`.

Per `feedback_lean_induction_universal_motive.md`: state the
`elseBranch`-side universal in the conclusion to keep the IH wide
across nested induction on the two branches. -/
theorem RawTerm.boolElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {thenBranch : RawTerm scope}
    (thenIsSN : RawTerm.isStronglyNormalizing thenBranch) :
    ∀ {elseBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing elseBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.boolElim (RawTerm.var position) thenBranch elseBranch) := by
  induction thenIsSN with
  | intro currentThen _ thenIH =>
    intro elseBranch elseIsSN
    induction elseIsSN with
    | intro currentElse elseClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.boolElim (RawTerm.var position) currentThen currentElse) ?_
      intro target progressStep
      rcases RawStep.par.boolElim_inv progressStep.1 with
        ⟨scrutineeTarget, thenTarget, elseTarget, targetEq,
          scrutineeStep, thenStep, elseStep⟩
        | (⟨thenTarget, _targetEq, scrutineeStep, _thenStep⟩
          | ⟨elseTarget, _targetEq, scrutineeStep, _elseStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases thenEq : currentThen = thenTarget
        · subst thenEq
          have elseDistinct :
              currentElse ≠ elseTarget := fun elseEq =>
            progressStep.2 (congrArg
              (RawTerm.boolElim (RawTerm.var position) currentThen) elseEq)
          exact innerIH elseTarget ⟨elseStep, elseDistinct⟩
        · have thenProgress :
              RawStep.parProgress currentThen thenTarget :=
            ⟨thenStep, thenEq⟩
          by_cases elseEq : currentElse = elseTarget
          · subst elseEq
            exact thenIH thenTarget thenProgress
              (RawTerm.isStronglyNormalizing.intro currentElse elseClosure)
          · exact thenIH thenTarget thenProgress
              (elseClosure elseTarget ⟨elseStep, elseEq⟩)
      · exact (by
          have varEqTrue :
              RawTerm.var position = RawTerm.boolTrue :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqTrue)
      · exact (by
          have varEqFalse :
              RawTerm.var position = RawTerm.boolFalse :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqFalse)

/-- Boolean eliminator SN preservation.  This is the generic version
behind the neutral `boolElim_var` helper: congruence arms recurse through
the three SN subterms, while true/false ι arms return the corresponding
branch target. -/
theorem RawTerm.boolElim_isStronglyNormalizing {scope : Nat}
    {thenBranch : RawTerm scope}
    (thenIsSN : RawTerm.isStronglyNormalizing thenBranch) :
    ∀ {elseBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing elseBranch →
    ∀ {scrutinee : RawTerm scope},
      RawTerm.isStronglyNormalizing scrutinee →
      RawTerm.isStronglyNormalizing
        (RawTerm.boolElim scrutinee thenBranch elseBranch) := by
  induction thenIsSN with
  | intro currentThen thenClosure thenIH =>
    intro elseBranch elseIsSN
    induction elseIsSN with
    | intro currentElse elseClosure elseIH =>
      intro scrutinee scrutineeIsSN
      induction scrutineeIsSN with
      | intro currentScrutinee scrutineeClosure scrutineeIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.boolElim currentScrutinee currentThen currentElse) ?_
        intro target progressStep
        cases RawStep.par.boolElim_inv progressStep.1 with
        | inl congruentStep =>
          rcases congruentStep with
            ⟨scrutineeTarget, thenTarget, elseTarget, targetEq,
              scrutineeStep, thenStep, elseStep⟩
          subst targetEq
          by_cases thenEq : currentThen = thenTarget
          · subst thenEq
            by_cases elseEq : currentElse = elseTarget
            · subst elseEq
              by_cases scrutineeEq : currentScrutinee = scrutineeTarget
              · subst scrutineeEq
                exact (progressStep.2 rfl).elim
              · exact scrutineeIH scrutineeTarget
                  ⟨scrutineeStep, scrutineeEq⟩
            · have scrutineeTargetIsSN :
                  RawTerm.isStronglyNormalizing scrutineeTarget := by
                by_cases scrutineeEq : currentScrutinee = scrutineeTarget
                · subst scrutineeEq
                  exact RawTerm.isStronglyNormalizing.intro currentScrutinee
                    scrutineeClosure
                · exact scrutineeClosure scrutineeTarget
                    ⟨scrutineeStep, scrutineeEq⟩
              exact elseIH elseTarget ⟨elseStep, elseEq⟩
                scrutineeTargetIsSN
          · have elseTargetIsSN :
                RawTerm.isStronglyNormalizing elseTarget := by
              by_cases elseEq : currentElse = elseTarget
              · subst elseEq
                exact RawTerm.isStronglyNormalizing.intro currentElse
                  elseClosure
              · exact elseClosure elseTarget ⟨elseStep, elseEq⟩
            have scrutineeTargetIsSN :
                RawTerm.isStronglyNormalizing scrutineeTarget := by
              by_cases scrutineeEq : currentScrutinee = scrutineeTarget
              · subst scrutineeEq
                exact RawTerm.isStronglyNormalizing.intro currentScrutinee
                  scrutineeClosure
              · exact scrutineeClosure scrutineeTarget
                  ⟨scrutineeStep, scrutineeEq⟩
            exact thenIH thenTarget ⟨thenStep, thenEq⟩
              elseTargetIsSN scrutineeTargetIsSN
        | inr iotaStep =>
          cases iotaStep with
          | inl trueStep =>
            rcases trueStep with
              ⟨thenTarget, targetEq, _scrutineeStep, thenStep⟩
            rw [targetEq]
            by_cases thenEq : currentThen = thenTarget
            · subst thenEq
              exact RawTerm.isStronglyNormalizing.intro currentThen
                thenClosure
            · exact thenClosure thenTarget ⟨thenStep, thenEq⟩
          | inr falseStep =>
            rcases falseStep with
              ⟨elseTarget, targetEq, _scrutineeStep, elseStep⟩
            rw [targetEq]
            by_cases elseEq : currentElse = elseTarget
            · subst elseEq
              exact RawTerm.isStronglyNormalizing.intro currentElse
                elseClosure
            · exact elseClosure elseTarget ⟨elseStep, elseEq⟩

/-- **K12.20.AV.1 neutral natElim SN preservation**.  Sister to
`boolElim_var`; nat-recursor with variable scrutinee.

Same nested-induction template as `boolElim_var`: variable
scrutinee blocks both ι rules (`iotaNatElimZero` requires
`var → natZero`, `iotaNatElimSucc` requires `var → natSucc _`),
the cong arm collapses to binary movement on (zeroBranch,
succBranch). -/
theorem RawTerm.natElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {zeroBranch : RawTerm scope}
    (zeroIsSN : RawTerm.isStronglyNormalizing zeroBranch) :
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.natElim (RawTerm.var position) zeroBranch succBranch) := by
  induction zeroIsSN with
  | intro currentZero _ zeroIH =>
    intro succBranch succIsSN
    induction succIsSN with
    | intro currentSucc succClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.natElim (RawTerm.var position) currentZero currentSucc) ?_
      intro target progressStep
      rcases RawStep.par.natElim_inv progressStep.1 with
        ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
          scrutineeStep, zeroStep, succStep⟩
        | (⟨zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
          | ⟨predRaw, succTarget, _targetEq, scrutineeStep, _succStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases zeroEq : currentZero = zeroTarget
        · subst zeroEq
          have succDistinct :
              currentSucc ≠ succTarget := fun succEq =>
            progressStep.2 (congrArg
              (RawTerm.natElim (RawTerm.var position) currentZero) succEq)
          exact innerIH succTarget ⟨succStep, succDistinct⟩
        · have zeroProgress :
              RawStep.parProgress currentZero zeroTarget :=
            ⟨zeroStep, zeroEq⟩
          by_cases succEq : currentSucc = succTarget
          · subst succEq
            exact zeroIH zeroTarget zeroProgress
              (RawTerm.isStronglyNormalizing.intro currentSucc succClosure)
          · exact zeroIH zeroTarget zeroProgress
              (succClosure succTarget ⟨succStep, succEq⟩)
      · exact (by
          have varEqZero :
              RawTerm.var position = RawTerm.natZero :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqZero)
      · exact (by
          have varEqSucc :
              RawTerm.var position = RawTerm.natSucc predRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqSucc)

/-- **K12.20.AV.2 neutral natRec SN preservation**.  Sister to
`natElim_var`; nat recursor (motive-dependent) with variable
scrutinee.  Same proof shape; the succ-ι rule rebuilds the
target into `app (app succ predRaw) (natRec predRaw zero succ)`
but inversion still requires `scrutinee → natSucc predRaw`,
which `var_inv` rules out. -/
theorem RawTerm.natRec_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {zeroBranch : RawTerm scope}
    (zeroIsSN : RawTerm.isStronglyNormalizing zeroBranch) :
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.natRec (RawTerm.var position) zeroBranch succBranch) := by
  induction zeroIsSN with
  | intro currentZero _ zeroIH =>
    intro succBranch succIsSN
    induction succIsSN with
    | intro currentSucc succClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.natRec (RawTerm.var position) currentZero currentSucc) ?_
      intro target progressStep
      rcases RawStep.par.natRec_inv progressStep.1 with
        ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
          scrutineeStep, zeroStep, succStep⟩
        | (⟨zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
          | ⟨predRaw, zeroTarget, succTarget,
              _targetEq, scrutineeStep, _zeroStep, _succStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases zeroEq : currentZero = zeroTarget
        · subst zeroEq
          have succDistinct :
              currentSucc ≠ succTarget := fun succEq =>
            progressStep.2 (congrArg
              (RawTerm.natRec (RawTerm.var position) currentZero) succEq)
          exact innerIH succTarget ⟨succStep, succDistinct⟩
        · have zeroProgress :
              RawStep.parProgress currentZero zeroTarget :=
            ⟨zeroStep, zeroEq⟩
          by_cases succEq : currentSucc = succTarget
          · subst succEq
            exact zeroIH zeroTarget zeroProgress
              (RawTerm.isStronglyNormalizing.intro currentSucc succClosure)
          · exact zeroIH zeroTarget zeroProgress
              (succClosure succTarget ⟨succStep, succEq⟩)
      · exact (by
          have varEqZero :
              RawTerm.var position = RawTerm.natZero :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqZero)
      · exact (by
          have varEqSucc :
              RawTerm.var position = RawTerm.natSucc predRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqSucc)


end LeanFX2
