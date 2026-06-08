import FX1Poly.Typed.CombinatoryLogic

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

def saTerm (a : RawTerm 0) : RawTerm 0 :=
  lamCell (lamCell (appCell
    (appCell (RawTerm.weaken (RawTerm.weaken a)) (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))
    (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
      (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))))

def sabTerm (a b : RawTerm 0) : RawTerm 0 :=
  lamCell (appCell
    (appCell (RawTerm.weaken a) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
    (appCell (RawTerm.weaken b) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))))

theorem skkReducesToIdentity (arg : RawTerm 0) :
    StepStar (appCell (appCell (appCell combinatorS combinatorK) combinatorK) arg) arg := by
  have step1 : Step (appCell (appCell (appCell combinatorS combinatorK) combinatorK) arg)
      (appCell (appCell (saTerm combinatorK) combinatorK) arg) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons arg .childNil)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            (.childCons combinatorK .childNil) Step.beta)))
  have step2 : Step (appCell (appCell (saTerm combinatorK) combinatorK) arg)
      (appCell (sabTerm combinatorK combinatorK) arg) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons arg .childNil) Step.beta)
  have step3 : Step (appCell (sabTerm combinatorK combinatorK) arg)
      (appCell (appCell combinatorK arg) (appCell combinatorK arg)) := Step.beta
  exact StepStar.trans step1 (StepStar.trans step2 (StepStar.trans step3
    (combinatorK_reduces arg (appCell combinatorK arg))))

end FX1Poly.Typed

#print axioms FX1Poly.Typed.skkReducesToIdentity
