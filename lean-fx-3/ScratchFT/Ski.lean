import FX1Poly.Typed.CurryFixpointDivergence
import FX1Poly.Core.RawTermSubst0Commute

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

def combinatorI : RawTerm 0 := lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))

def combinatorK : RawTerm 0 :=
  lamCell (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))

def combinatorS : RawTerm 0 :=
  lamCell (lamCell (lamCell
    (appCell
      (appCell (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))
        (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))
      (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
        (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))))))

theorem combinatorI_stronglyNormalizing : IsStronglyNormalizing combinatorI :=
  isStronglyNormalizing_of_noStep (fun target stp =>
    RawTerm.isStepNormalForm_blocks_step (by decide) target stp)

theorem combinatorK_stronglyNormalizing : IsStronglyNormalizing combinatorK :=
  isStronglyNormalizing_of_noStep (fun target stp =>
    RawTerm.isStepNormalForm_blocks_step (by decide) target stp)

theorem combinatorS_stronglyNormalizing : IsStronglyNormalizing combinatorS :=
  isStronglyNormalizing_of_noStep (fun target stp =>
    RawTerm.isStepNormalForm_blocks_step (by decide) target stp)

theorem combinatorI_reduces (a : RawTerm 0) : Step (appCell combinatorI a) a := Step.beta

theorem combinatorK_reduces (a b : RawTerm 0) : StepStar (appCell (appCell combinatorK a) b) a := by
  have functionBeta : Step (appCell combinatorK a) (lamCell (RawTerm.weaken a)) := Step.beta
  have congStep : Step (appCell (appCell combinatorK a) b) (appCell (lamCell (RawTerm.weaken a)) b) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons b .childNil) functionBeta)
  have cancelEq : RawTerm.subst0 (RawTerm.weaken a) b = a := RawTerm.weaken_subst_singleton a b
  have outerBeta : Step (appCell (lamCell (RawTerm.weaken a)) b) (RawTerm.subst0 (RawTerm.weaken a) b) :=
    Step.beta
  rw [cancelEq] at outerBeta
  exact StepStar.trans congStep (StepStar.trans outerBeta (StepStar.refl _))

end FX1Poly.Typed

#print axioms FX1Poly.Typed.combinatorI_stronglyNormalizing
#print axioms FX1Poly.Typed.combinatorK_stronglyNormalizing
#print axioms FX1Poly.Typed.combinatorS_stronglyNormalizing
#print axioms FX1Poly.Typed.combinatorI_reduces
#print axioms FX1Poly.Typed.combinatorK_reduces
