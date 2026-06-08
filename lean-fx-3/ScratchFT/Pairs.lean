import FX1Poly.Typed.CombinatoryLogic
import FX1Poly.Core.RawTermSubst0Commute

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

def pairTerm (a b : RawTerm 0) : RawTerm 0 :=
  lamCell (appCell (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken a))
    (RawTerm.weaken b))

def churchFst : RawTerm 0 :=
  lamCell (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken combinatorK))

def secondProjector : RawTerm 0 :=
  lamCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))

def churchSnd : RawTerm 0 :=
  lamCell (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken secondProjector))

theorem secondProjector_reduces (a b : RawTerm 0) :
    StepStar (appCell (appCell secondProjector a) b) b := by
  have functionBeta : Step (appCell secondProjector a) combinatorI := Step.beta
  have congStep : Step (appCell (appCell secondProjector a) b) (appCell combinatorI b) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons b .childNil) functionBeta)
  exact StepStar.trans congStep (StepStar.trans (combinatorI_reduces b) (StepStar.refl _))

theorem pairFst_reduces (a b : RawTerm 0) :
    StepStar (appCell churchFst (pairTerm a b)) a := by
  have step1 : Step (appCell churchFst (pairTerm a b)) (appCell (pairTerm a b) combinatorK) := Step.beta
  have step2 : Step (appCell (pairTerm a b) combinatorK)
      (appCell (appCell combinatorK (RawTerm.subst0 (RawTerm.weaken a) combinatorK))
        (RawTerm.subst0 (RawTerm.weaken b) combinatorK)) := Step.beta
  have cancelA : RawTerm.subst0 (RawTerm.weaken a) combinatorK = a := RawTerm.weaken_subst_singleton a combinatorK
  have cancelB : RawTerm.subst0 (RawTerm.weaken b) combinatorK = b := RawTerm.weaken_subst_singleton b combinatorK
  rw [cancelA, cancelB] at step2
  exact StepStar.trans step1 (StepStar.trans step2 (combinatorK_reduces a b))

theorem pairSnd_reduces (a b : RawTerm 0) :
    StepStar (appCell churchSnd (pairTerm a b)) b := by
  have step1 : Step (appCell churchSnd (pairTerm a b)) (appCell (pairTerm a b) secondProjector) := Step.beta
  have step2 : Step (appCell (pairTerm a b) secondProjector)
      (appCell (appCell secondProjector (RawTerm.subst0 (RawTerm.weaken a) secondProjector))
        (RawTerm.subst0 (RawTerm.weaken b) secondProjector)) := Step.beta
  have cancelA : RawTerm.subst0 (RawTerm.weaken a) secondProjector = a :=
    RawTerm.weaken_subst_singleton a secondProjector
  have cancelB : RawTerm.subst0 (RawTerm.weaken b) secondProjector = b :=
    RawTerm.weaken_subst_singleton b secondProjector
  rw [cancelA, cancelB] at step2
  exact StepStar.trans step1 (StepStar.trans step2 (secondProjector_reduces a b))

end FX1Poly.Typed

#print axioms FX1Poly.Typed.secondProjector_reduces
#print axioms FX1Poly.Typed.pairFst_reduces
#print axioms FX1Poly.Typed.pairSnd_reduces
