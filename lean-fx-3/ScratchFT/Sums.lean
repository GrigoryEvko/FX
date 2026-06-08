import FX1Poly.Typed.CombinatoryLogic
import FX1Poly.Core.RawTermSubst0Commute

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

-- leftInjection a = λl. λr. l a ; rightInjection b = λl. λr. r b
def leftInjection (a : RawTerm 0) : RawTerm 0 :=
  lamCell (lamCell (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
    (RawTerm.weaken (RawTerm.weaken a))))

def rightInjection (b : RawTerm 0) : RawTerm 0 :=
  lamCell (lamCell (appCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))
    (RawTerm.weaken (RawTerm.weaken b))))

-- case s l r = s l r ;  case (inl c) l r ↝* l c   (concrete stored value combinatorI)
theorem caseLeft_selectsLeftHandler (handlerL handlerR : RawTerm 0) :
    StepStar (appCell (appCell (leftInjection combinatorI) handlerL) handlerR)
      (appCell handlerL combinatorI) := by
  have functionBeta : Step (appCell (leftInjection combinatorI) handlerL)
      (lamCell (appCell (RawTerm.weaken handlerL) (RawTerm.weaken combinatorI))) := Step.beta
  have congStep : Step (appCell (appCell (leftInjection combinatorI) handlerL) handlerR)
      (appCell (lamCell (appCell (RawTerm.weaken handlerL) (RawTerm.weaken combinatorI))) handlerR) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons handlerR .childNil) functionBeta)
  have outerBeta : Step (appCell (lamCell (appCell (RawTerm.weaken handlerL) (RawTerm.weaken combinatorI))) handlerR)
      (appCell (RawTerm.subst0 (RawTerm.weaken handlerL) handlerR)
        (RawTerm.subst0 (RawTerm.weaken combinatorI) handlerR)) := Step.beta
  have cancelHandler : RawTerm.subst0 (RawTerm.weaken handlerL) handlerR = handlerL :=
    RawTerm.weaken_subst_singleton handlerL handlerR
  have cancelValue : RawTerm.subst0 (RawTerm.weaken combinatorI) handlerR = combinatorI :=
    RawTerm.weaken_subst_singleton combinatorI handlerR
  rw [cancelHandler, cancelValue] at outerBeta
  exact StepStar.trans congStep (StepStar.trans outerBeta (StepStar.refl _))

theorem caseRight_selectsRightHandler (handlerL handlerR : RawTerm 0) :
    StepStar (appCell (appCell (rightInjection combinatorI) handlerL) handlerR)
      (appCell handlerR combinatorI) := by
  have functionBeta : Step (appCell (rightInjection combinatorI) handlerL)
      (lamCell (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken combinatorI))) := Step.beta
  have congStep : Step (appCell (appCell (rightInjection combinatorI) handlerL) handlerR)
      (appCell (lamCell (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken combinatorI))) handlerR) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons handlerR .childNil) functionBeta)
  have outerBeta : Step (appCell (lamCell (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken combinatorI))) handlerR)
      (appCell handlerR (RawTerm.subst0 (RawTerm.weaken combinatorI) handlerR)) := Step.beta
  have cancelValue : RawTerm.subst0 (RawTerm.weaken combinatorI) handlerR = combinatorI :=
    RawTerm.weaken_subst_singleton combinatorI handlerR
  rw [cancelValue] at outerBeta
  exact StepStar.trans congStep (StepStar.trans outerBeta (StepStar.refl _))

end FX1Poly.Typed

#print axioms FX1Poly.Typed.caseLeft_selectsLeftHandler
#print axioms FX1Poly.Typed.caseRight_selectsRightHandler
