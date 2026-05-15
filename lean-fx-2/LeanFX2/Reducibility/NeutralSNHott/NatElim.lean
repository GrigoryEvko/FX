import LeanFX2.Reducibility.NeutralSNHott.ElimVarShape
import LeanFX2.Term.SN.Helpers

/-! # LeanFX2.Reducibility.NeutralSNHott.NatElim

Generic `natElim` SN preservation (raw + Term wrapper) consumed by
the Kripke fundamental headline.  The earlier per-canonical-form
helpers (`_natZero` / `_natSucc`) were Tait-era scaffolding and are
not used by the Kripke pivot. -/

namespace LeanFX2

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
