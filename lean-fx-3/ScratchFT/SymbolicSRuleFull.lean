import FX1Poly.Typed.CombinatoryCompleteness
import FX1Poly.Core.RawTermSubstLiftWeaken

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

-- R_sab: the β2 contractum reshape (uses the double-weaken cancellation).
theorem Rsab (a b : RawTerm 0) :
    RawTerm.subst0
        (lamCell (appCell
          (appCell (RawTerm.weaken (RawTerm.weaken a)) (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))
          (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))) b
      = sabTerm a b := by
  unfold RawTerm.subst0 sabTerm
  show lamCell (appCell
      (appCell (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton b))
        (RawTerm.weaken (RawTerm.weaken a))) _) _) = _
  rw [RawTerm.subst_lift_singleton_weaken_weaken a b]
  rfl

-- R_final: the β3 contractum reshape (single-weaken cancellations).
theorem Rfinal (a b c : RawTerm 0) :
    RawTerm.subst0
        (appCell (appCell (RawTerm.weaken a) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
          (appCell (RawTerm.weaken b) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) c
      = appCell (appCell a c) (appCell b c) := by
  unfold RawTerm.subst0
  show appCell (appCell (RawTerm.subst (RawTermSubst.singleton c) (RawTerm.weaken a)) _)
      (appCell (RawTerm.subst (RawTermSubst.singleton c) (RawTerm.weaken b)) _) = _
  rw [RawTerm.weaken_subst_singleton a c, RawTerm.weaken_subst_singleton b c]
  rfl

-- ★ The general symbolic S-rule.
theorem combinatorS_appliedReducesToIterate (a b c : RawTerm 0) :
    StepStar (appCell (appCell (appCell combinatorS a) b) c)
      (appCell (appCell a c) (appCell b c)) := by
  have step1 : Step (appCell combinatorS a) (saTerm a) := Step.beta
  have step2 : Step (appCell (saTerm a) b) (sabTerm a b) := by
    rw [← Rsab a b]; exact Step.beta
  have step3 : Step (appCell (sabTerm a b) c) (appCell (appCell a c) (appCell b c)) := by
    rw [← Rfinal a b c]; exact Step.beta
  exact StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons c .childNil)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            (.childCons b .childNil) step1))))
    (StepStar.trans
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
          (.childCons c .childNil) step2))
      (StepStar.trans step3 (StepStar.refl _)))

end FX1Poly.Typed

#print axioms FX1Poly.Typed.Rsab
#print axioms FX1Poly.Typed.Rfinal
#print axioms FX1Poly.Typed.combinatorS_appliedReducesToIterate
