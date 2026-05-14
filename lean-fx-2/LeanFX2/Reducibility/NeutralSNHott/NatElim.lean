import LeanFX2.Reducibility.NeutralSNHott.ElimVarShape
import LeanFX2.Reducibility.SNHelpers

/-! # LeanFX2.Reducibility.NeutralSNHott.NatElim

K12.20.AZ natElim SN preservation: `natElim_natZero` /
`natElim_natSucc` / `natElim` (raw + Term wrappers).

## Root status

Layer 3 metatheory leaf.  Third slice of NeutralSNHott. -/

namespace LeanFX2


/-- Nat-zero ι SN expansion for `natElim`.

For a canonical zero scrutinee, `natElim` reduces to the zero branch.
The successor branch remains in the statement because congruent
reductions may step under it before the ι rule fires. -/
theorem RawTerm.natElim_natZero_isStronglyNormalizing
    {scope : Nat}
    {zeroBranch : RawTerm scope}
    (zeroIsSN : RawTerm.isStronglyNormalizing zeroBranch) :
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.natElim RawTerm.natZero zeroBranch succBranch) := by
  induction zeroIsSN with
  | intro currentZero zeroClosure zeroIH =>
    intro succBranch succIsSN
    induction succIsSN with
    | intro currentSucc succClosure succIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.natElim RawTerm.natZero currentZero currentSucc) ?_
      intro target progressStep
      rcases RawStep.par.natElim_inv progressStep.1 with
        ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
          scrutineeStep, zeroStep, succStep⟩
        | ⟨zeroTarget, targetEq, _scrutineeStep, zeroStep⟩
        | ⟨predecessorTarget, _succTarget, _targetEq,
            scrutineeStep, _succStep⟩
      · have scrutineeTargetEq :
            scrutineeTarget = (RawTerm.natZero : RawTerm scope) :=
          RawStep.par.natZero_inv scrutineeStep
        subst scrutineeTargetEq
        subst targetEq
        by_cases zeroEq : currentZero = zeroTarget
        · subst zeroEq
          by_cases succEq : currentSucc = succTarget
          · subst succEq
            exact (progressStep.2 rfl).elim
          · exact succIH succTarget ⟨succStep, succEq⟩
        · have succTargetIsSN :
              RawTerm.isStronglyNormalizing succTarget := by
            by_cases succEq : currentSucc = succTarget
            · subst succEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSucc succClosure
            · exact succClosure succTarget ⟨succStep, succEq⟩
          exact zeroIH zeroTarget ⟨zeroStep, zeroEq⟩ succTargetIsSN
      · rw [targetEq]
        by_cases zeroEq : currentZero = zeroTarget
        · subst zeroEq
          exact RawTerm.isStronglyNormalizing.intro currentZero zeroClosure
        · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
      · have succEqZero :
            RawTerm.natSucc predecessorTarget =
              (RawTerm.natZero : RawTerm scope) :=
          RawStep.par.natZero_inv scrutineeStep
        nomatch succEqZero

/-- Typed nat-zero ι SN expansion for `Term.natElim`. -/
theorem Term.natElim_natZero_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw}
    (zeroIsSN : Term.isStronglyNormalizing zeroBranch)
    (succIsSN : Term.isStronglyNormalizing succBranch) :
    Term.isStronglyNormalizing
      (Term.natElim Term.natZero zeroBranch succBranch) :=
  RawTerm.natElim_natZero_isStronglyNormalizing
    zeroIsSN succIsSN

/-- Nat-successor ι SN expansion for `natElim`.

For a canonical successor scrutinee, `natElim` reduces to
`succBranch predecessor`.  The zero branch remains explicit because
congruent reductions may step under it before the ι rule fires. -/
theorem RawTerm.natElim_natSucc_isStronglyNormalizing
    {scope : Nat}
    {predecessor : RawTerm scope}
    (predecessorIsSN : RawTerm.isStronglyNormalizing predecessor) :
    ∀ {zeroBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing zeroBranch →
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.app succBranch predecessor) →
      RawTerm.isStronglyNormalizing
        (RawTerm.natElim
          (RawTerm.natSucc predecessor) zeroBranch succBranch) := by
  induction predecessorIsSN with
  | intro currentPredecessor predecessorClosure predecessorIH =>
    intro zeroBranch zeroIsSN
    induction zeroIsSN with
    | intro currentZero zeroClosure zeroIH =>
      intro succBranch succIsSN succAppIsSN
      induction succIsSN with
      | intro currentSucc succClosure succIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.natElim
            (RawTerm.natSucc currentPredecessor)
            currentZero currentSucc) ?_
        intro target progressStep
        rcases RawStep.par.natElim_inv progressStep.1 with
          ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
            scrutineeStep, zeroStep, succStep⟩
          | ⟨zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
          | ⟨predecessorTarget, succTarget, targetEq,
              scrutineeStep, succStep⟩
        · obtain ⟨predecessorTarget, scrutineeTargetEq,
              predecessorStep⟩ :=
            RawStep.par.natSucc_inv scrutineeStep
          subst scrutineeTargetEq
          subst targetEq
          have predecessorTargetIsSN :
              RawTerm.isStronglyNormalizing predecessorTarget := by
            by_cases predecessorEq :
                currentPredecessor = predecessorTarget
            · subst predecessorEq
              exact RawTerm.isStronglyNormalizing.intro
                currentPredecessor predecessorClosure
            · exact predecessorClosure predecessorTarget
                ⟨predecessorStep, predecessorEq⟩
          have zeroTargetIsSN :
              RawTerm.isStronglyNormalizing zeroTarget := by
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              exact RawTerm.isStronglyNormalizing.intro
                currentZero zeroClosure
            · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
          have succTargetIsSN :
              RawTerm.isStronglyNormalizing succTarget := by
            by_cases succEq : currentSucc = succTarget
            · subst succEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSucc succClosure
            · exact succClosure succTarget ⟨succStep, succEq⟩
          have succAppTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.app succTarget predecessorTarget) := by
            by_cases appEq :
                RawTerm.app currentSucc currentPredecessor =
                  RawTerm.app succTarget predecessorTarget
            · rw [← appEq]
              exact succAppIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                succAppIsSN
                ⟨RawStep.par.app succStep predecessorStep, appEq⟩
          by_cases predecessorEq : currentPredecessor = predecessorTarget
          · subst predecessorEq
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              by_cases succEq : currentSucc = succTarget
              · subst succEq
                exact (progressStep.2 rfl).elim
              · exact succIH succTarget ⟨succStep, succEq⟩
                  succAppTargetIsSN
            · exact zeroIH zeroTarget ⟨zeroStep, zeroEq⟩
                succTargetIsSN succAppTargetIsSN
          · exact predecessorIH predecessorTarget
              ⟨predecessorStep, predecessorEq⟩
              zeroTargetIsSN succTargetIsSN succAppTargetIsSN
        · obtain ⟨_predecessorTarget, natZeroEq, _predecessorStep⟩ :=
            RawStep.par.natSucc_inv scrutineeStep
          nomatch natZeroEq
        · obtain ⟨_predecessorTargetFromScrutinee, successorEq,
              predecessorStep⟩ :=
            RawStep.par.natSucc_inv scrutineeStep
          injection successorEq with _scopeEq predecessorTargetEq
          subst targetEq
          have predecessorStepToTarget :
              RawStep.par currentPredecessor predecessorTarget := by
            rw [predecessorTargetEq]
            exact predecessorStep
          have succAppTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.app succTarget predecessorTarget) := by
            by_cases appEq :
                RawTerm.app currentSucc currentPredecessor =
                  RawTerm.app succTarget predecessorTarget
            · rw [← appEq]
              exact succAppIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                succAppIsSN
                ⟨RawStep.par.app succStep predecessorStepToTarget, appEq⟩
          exact succAppTargetIsSN

/-- Typed nat-successor ι SN expansion for `Term.natElim`. -/
theorem Term.natElim_natSucc_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    {predecessor : Term context Ty.nat predecessorRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw}
    (predecessorIsSN : Term.isStronglyNormalizing predecessor)
    (zeroIsSN : Term.isStronglyNormalizing zeroBranch)
    (succIsSN : Term.isStronglyNormalizing succBranch)
    (succAppIsSN :
      Term.isStronglyNormalizing
        (Term.app succBranch predecessor)) :
    Term.isStronglyNormalizing
      (Term.natElim
        (Term.natSucc predecessor) zeroBranch succBranch) :=
  RawTerm.natElim_natSucc_isStronglyNormalizing
    predecessorIsSN zeroIsSN succIsSN succAppIsSN

/-- General SN preservation for `natElim`.

The successor branch is supplied through a raw SN closure over every
strongly-normalizing predecessor.  This is the exact information needed
by the deep successor ι arm of `RawStep.par.natElim_inv`, where the
scrutinee may develop to `natSucc predecessor` before the eliminator
fires. -/
theorem RawTerm.natElim_isStronglyNormalizing {scope : Nat}
    {scrutinee : RawTerm scope}
    (scrutineeIsSN : RawTerm.isStronglyNormalizing scrutinee) :
    ∀ {zeroBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing zeroBranch →
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      (∀ {predecessor : RawTerm scope},
        RawTerm.isStronglyNormalizing predecessor →
        RawTerm.isStronglyNormalizing
          (RawTerm.app succBranch predecessor)) →
      RawTerm.isStronglyNormalizing
        (RawTerm.natElim scrutinee zeroBranch succBranch) := by
  induction scrutineeIsSN with
  | intro currentScrutinee scrutineeClosure scrutineeIH =>
    intro zeroBranch zeroIsSN
    induction zeroIsSN with
    | intro currentZero zeroClosure zeroIH =>
      intro succBranch succIsSN succAppIsSN
      induction succIsSN with
      | intro currentSucc succClosure succIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.natElim currentScrutinee currentZero currentSucc) ?_
        intro target progressStep
        rcases RawStep.par.natElim_inv progressStep.1 with
          ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
            scrutineeStep, zeroStep, succStep⟩
          | ⟨zeroTarget, targetEq, scrutineeStep, zeroStep⟩
          | ⟨predecessorTarget, succTarget, targetEq,
              scrutineeStep, succStep⟩
        · subst targetEq
          have scrutineeTargetIsSN :
              RawTerm.isStronglyNormalizing scrutineeTarget := by
            by_cases scrutineeEq : currentScrutinee = scrutineeTarget
            · subst scrutineeEq
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact scrutineeClosure scrutineeTarget
                ⟨scrutineeStep, scrutineeEq⟩
          have zeroTargetIsSN :
              RawTerm.isStronglyNormalizing zeroTarget := by
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              exact RawTerm.isStronglyNormalizing.intro
                currentZero zeroClosure
            · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
          have succTargetIsSN :
              RawTerm.isStronglyNormalizing succTarget := by
            by_cases succEq : currentSucc = succTarget
            · subst succEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSucc succClosure
            · exact succClosure succTarget ⟨succStep, succEq⟩
          have succTargetAppIsSN :
              ∀ {predecessor : RawTerm scope},
                RawTerm.isStronglyNormalizing predecessor →
                RawTerm.isStronglyNormalizing
                  (RawTerm.app succTarget predecessor) := by
            intro predecessor predecessorIsSN
            by_cases appEq :
                RawTerm.app currentSucc predecessor =
                  RawTerm.app succTarget predecessor
            · rw [← appEq]
              exact succAppIsSN predecessorIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                (succAppIsSN predecessorIsSN)
                ⟨RawStep.par.app succStep (RawStep.par.refl predecessor),
                  appEq⟩
          by_cases scrutineeEq : currentScrutinee = scrutineeTarget
          · subst scrutineeEq
            by_cases zeroEq : currentZero = zeroTarget
            · subst zeroEq
              by_cases succEq : currentSucc = succTarget
              · subst succEq
                exact (progressStep.2 rfl).elim
              · exact succIH succTarget ⟨succStep, succEq⟩
                  succTargetAppIsSN
            · exact zeroIH zeroTarget ⟨zeroStep, zeroEq⟩
                succTargetIsSN succTargetAppIsSN
          · exact scrutineeIH scrutineeTarget
              ⟨scrutineeStep, scrutineeEq⟩
              zeroTargetIsSN succTargetIsSN succTargetAppIsSN
        · rw [targetEq]
          by_cases zeroEq : currentZero = zeroTarget
          · subst zeroEq
            exact RawTerm.isStronglyNormalizing.intro
              currentZero zeroClosure
          · exact zeroClosure zeroTarget ⟨zeroStep, zeroEq⟩
        · subst targetEq
          have successorScrutineeIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.natSucc predecessorTarget) := by
            by_cases scrutineeEq :
                currentScrutinee = RawTerm.natSucc predecessorTarget
            · rw [← scrutineeEq]
              exact RawTerm.isStronglyNormalizing.intro
                currentScrutinee scrutineeClosure
            · exact RawTerm.isStronglyNormalizing.step_preserves
                (RawTerm.isStronglyNormalizing.intro
                  currentScrutinee scrutineeClosure)
                ⟨scrutineeStep, scrutineeEq⟩
          have predecessorIsSN :
              RawTerm.isStronglyNormalizing predecessorTarget :=
            RawTerm.natSucc_predecessor_isStronglyNormalizing
              successorScrutineeIsSN
          by_cases appEq :
              RawTerm.app currentSucc predecessorTarget =
                RawTerm.app succTarget predecessorTarget
          · rw [← appEq]
            exact succAppIsSN predecessorIsSN
          · exact RawTerm.isStronglyNormalizing.step_preserves
              (succAppIsSN predecessorIsSN)
              ⟨RawStep.par.app succStep
                (RawStep.par.refl predecessorTarget), appEq⟩

/-- Typed wrapper for general `natElim` SN preservation. -/
theorem Term.natElim_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term context Ty.nat scrutineeRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (zeroIsSN : Term.isStronglyNormalizing zeroBranch)
    (succIsSN : Term.isStronglyNormalizing succBranch)
    (succAppIsSN :
      ∀ {predecessorRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing predecessorRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app succRaw predecessorRaw)) :
    Term.isStronglyNormalizing
      (Term.natElim scrutinee zeroBranch succBranch) :=
  RawTerm.natElim_isStronglyNormalizing
    scrutineeIsSN zeroIsSN succIsSN succAppIsSN


end LeanFX2
