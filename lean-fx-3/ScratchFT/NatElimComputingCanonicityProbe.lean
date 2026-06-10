import FX1Poly.Typed.ClosedNatCanonicity
import FX1Poly.Typed.HasTypeDescPi

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- natElim cell. -/
def natElimCell {scope : Nat} (scrutinee zeroBranch succBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_natElim ()
    (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))

-- Probe 0: does the iotaNatElimSucc reduct match appCell/natElimCell up to defeq?
example {predecessor zeroBranch succBranch : RawTerm 0} :
    Step (natElimCell (natSuccCell predecessor) zeroBranch succBranch)
      (appCell (appCell succBranch predecessor) (natElimCell predecessor zeroBranch succBranch)) :=
  Step.iotaNatElimSucc

-- Probe 0b: zero case
example {zeroBranch succBranch : RawTerm 0} :
    Step (natElimCell natZeroCell zeroBranch succBranch) zeroBranch :=
  Step.iotaNatElimZero

-- Probe 1: the ABSTRACT recursive computing canonicity.
theorem natElimComputesToNumeral_probe {zeroBranch succBranch : RawTerm 0}
    (zeroBranchNumeral : IsNatNumeral zeroBranch)
    (stepProduces : ∀ (predecessor recResult : RawTerm 0),
        IsNatNumeral predecessor → IsNatNumeral recResult →
        ∃ out : RawTerm 0,
          StepStar (appCell (appCell succBranch predecessor) recResult) out ∧ IsNatNumeral out)
    {scrutinee : RawTerm 0} (scrutineeNumeral : IsNatNumeral scrutinee) :
    ∃ out : RawTerm 0, StepStar (natElimCell scrutinee zeroBranch succBranch) out ∧ IsNatNumeral out := by
  induction scrutineeNumeral with
  | zero =>
      exact ⟨zeroBranch, StepStar.single Step.iotaNatElimZero, zeroBranchNumeral⟩
  | @succ predecessor predNumeral ih =>
      obtain ⟨recResult, recChain, recNumeral⟩ := ih
      obtain ⟨out, stepChain, outNumeral⟩ := stepProduces predecessor recResult predNumeral recNumeral
      refine ⟨out, ?_, outNumeral⟩
      have iotaStep :
          StepStar (natElimCell (natSuccCell predecessor) zeroBranch succBranch)
            (appCell (appCell succBranch predecessor)
              (natElimCell predecessor zeroBranch succBranch)) :=
        StepStar.single Step.iotaNatElimSucc
      have congStep :
          StepStar (appCell (appCell succBranch predecessor)
              (natElimCell predecessor zeroBranch succBranch))
            (appCell (appCell succBranch predecessor) recResult) :=
        StepStar.appArgument (appCell succBranch predecessor) recChain
      exact StepStar.trans_compose iotaStep (StepStar.trans_compose congStep stepChain)

-- The constant-zero step `λ_. λ_. natZero`.
def constNatZeroStep : RawTerm 0 := lamCell (lamCell (natZeroCell : RawTerm 2))

-- Probe 2a: subst0 through the outer binder on the closed inner lambda body.
example (pred : RawTerm 0) :
    RawTerm.subst0 (lamCell (natZeroCell : RawTerm 2)) pred = lamCell natZeroCell := by rfl

-- Probe 2b: subst0 on the nullary closed body (the second β).
example (rec : RawTerm 0) :
    RawTerm.subst0 (natZeroCell : RawTerm 1) rec = natZeroCell := by rfl

-- Probe 3: the concrete stepProduces for constNatZeroStep — applying to any 2 args lands natZero.
example (pred rec : RawTerm 0) :
    StepStar (appCell (appCell constNatZeroStep pred) rec) natZeroCell := by
  have beta1 : Step (appCell constNatZeroStep pred) (lamCell natZeroCell) := Step.beta
  have beta2 : Step (appCell (lamCell (natZeroCell : RawTerm 1)) rec) natZeroCell := Step.beta
  exact StepStar.trans_compose
    (StepStar.appFunction (StepStar.single beta1))
    (StepStar.single beta2)

-- The copy/successor step `λ_. λr. natSucc r` (var 0 = the recursive result `r`).
def copyNatStep : RawTerm 0 :=
  lamCell (lamCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 2))))

-- Probe 5: the full copy-fold concrete canonicity via the abstract theorem.
example {scrutinee : RawTerm 0} (scrutineeNumeral : IsNatNumeral scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (natElimCell scrutinee natZeroCell copyNatStep) out ∧ IsNatNumeral out :=
  natElimComputesToNumeral_probe
    (zeroBranch := natZeroCell) (succBranch := copyNatStep)
    IsNatNumeral.zero
    (fun pred rec _predNumeral recNumeral =>
      ⟨natSuccCell rec, by
        have beta1 : Step (appCell copyNatStep pred)
            (lamCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 1)))) := Step.beta
        have beta2 : Step (appCell (lamCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 1)))) rec)
            (natSuccCell rec) := Step.beta
        exact StepStar.trans_compose
          (StepStar.appFunction (StepStar.single beta1))
          (StepStar.single beta2),
        IsNatNumeral.succ recNumeral⟩)
    scrutineeNumeral

end FX1Poly.Typed

#print axioms FX1Poly.Typed.natElimComputesToNumeral_probe
