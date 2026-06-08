import FX1Poly.Typed.ChurchSums
import FX1Poly.Core.RawTermSubstLiftWeaken

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

-- β1 reshape for leftInjection at a SYMBOLIC payload (uses the double-weaken cancellation).
theorem leftInjection_subst_handlerL (payload handlerL : RawTerm 0) :
    RawTerm.subst0
        (lamCell (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
          (RawTerm.weaken (RawTerm.weaken payload)))) handlerL
      = lamCell (appCell (RawTerm.weaken handlerL) (RawTerm.weaken payload)) := by
  unfold RawTerm.subst0
  show lamCell (appCell _ (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton handlerL))
      (RawTerm.weaken (RawTerm.weaken payload)))) = _
  rw [RawTerm.subst_lift_singleton_weaken_weaken payload handlerL]
  rfl

-- β1 reshape for rightInjection at a SYMBOLIC payload.
theorem rightInjection_subst_handlerL (payload handlerL : RawTerm 0) :
    RawTerm.subst0
        (lamCell (appCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))
          (RawTerm.weaken (RawTerm.weaken payload)))) handlerL
      = lamCell (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken payload)) := by
  unfold RawTerm.subst0
  show lamCell (appCell _ (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton handlerL))
      (RawTerm.weaken (RawTerm.weaken payload)))) = _
  rw [RawTerm.subst_lift_singleton_weaken_weaken payload handlerL]
  rfl

theorem caseLeft_selectsLeftHandler_general (payload handlerL handlerR : RawTerm 0) :
    StepStar (appCell (appCell (leftInjection payload) handlerL) handlerR)
      (appCell handlerL payload) := by
  have functionBeta : Step (appCell (leftInjection payload) handlerL)
      (lamCell (appCell (RawTerm.weaken handlerL) (RawTerm.weaken payload))) := by
    rw [← leftInjection_subst_handlerL payload handlerL]; exact Step.beta
  have congStep : Step (appCell (appCell (leftInjection payload) handlerL) handlerR)
      (appCell (lamCell (appCell (RawTerm.weaken handlerL) (RawTerm.weaken payload))) handlerR) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons handlerR .childNil) functionBeta)
  have outerBeta : Step (appCell (lamCell (appCell (RawTerm.weaken handlerL) (RawTerm.weaken payload))) handlerR)
      (appCell (RawTerm.subst0 (RawTerm.weaken handlerL) handlerR)
        (RawTerm.subst0 (RawTerm.weaken payload) handlerR)) := Step.beta
  have cancelHandler : RawTerm.subst0 (RawTerm.weaken handlerL) handlerR = handlerL :=
    RawTerm.weaken_subst_singleton handlerL handlerR
  have cancelValue : RawTerm.subst0 (RawTerm.weaken payload) handlerR = payload :=
    RawTerm.weaken_subst_singleton payload handlerR
  rw [cancelHandler, cancelValue] at outerBeta
  exact StepStar.trans congStep (StepStar.trans outerBeta (StepStar.refl _))

theorem caseRight_selectsRightHandler_general (payload handlerL handlerR : RawTerm 0) :
    StepStar (appCell (appCell (rightInjection payload) handlerL) handlerR)
      (appCell handlerR payload) := by
  have functionBeta : Step (appCell (rightInjection payload) handlerL)
      (lamCell (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken payload))) := by
    rw [← rightInjection_subst_handlerL payload handlerL]; exact Step.beta
  have congStep : Step (appCell (appCell (rightInjection payload) handlerL) handlerR)
      (appCell (lamCell (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken payload))) handlerR) :=
    Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons handlerR .childNil) functionBeta)
  have outerBeta : Step (appCell (lamCell (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (RawTerm.weaken payload))) handlerR)
      (appCell handlerR (RawTerm.subst0 (RawTerm.weaken payload) handlerR)) := Step.beta
  have cancelValue : RawTerm.subst0 (RawTerm.weaken payload) handlerR = payload :=
    RawTerm.weaken_subst_singleton payload handlerR
  rw [cancelValue] at outerBeta
  exact StepStar.trans congStep (StepStar.trans outerBeta (StepStar.refl _))

theorem caseSelectsByTag_general (payload handlerL handlerR : RawTerm 0) :
    StepStar (appCell (appCell (leftInjection payload) handlerL) handlerR) (appCell handlerL payload)
    ∧ StepStar (appCell (appCell (rightInjection payload) handlerL) handlerR) (appCell handlerR payload) :=
  ⟨caseLeft_selectsLeftHandler_general payload handlerL handlerR,
   caseRight_selectsRightHandler_general payload handlerL handlerR⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.caseLeft_selectsLeftHandler_general
#print axioms FX1Poly.Typed.caseRight_selectsRightHandler_general
#print axioms FX1Poly.Typed.caseSelectsByTag_general
