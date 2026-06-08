import FX1Poly.Typed.TypedChurchNumeralFaithful
import FX1Poly.Typed.TypedChurchNumeralInhabitants
import FX1Poly.Core.RawTermSubst0Commute

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

theorem iteratedApplication_subst0_weaken_step (depth : Nat) (stepFn base : RawTerm 0) :
    RawTerm.subst0 (iteratedApplication depth (RawTerm.weaken stepFn)
        (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) base
      = iteratedApplication depth stepFn base := by
  unfold RawTerm.subst0
  rw [subst_iteratedApplication]
  have stepEq : RawTerm.subst (RawTermSubst.singleton base) (RawTerm.weaken stepFn) = stepFn :=
    RawTerm.weaken_subst_singleton stepFn base
  have baseEq : RawTerm.subst (RawTermSubst.singleton base)
      (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) = base := rfl
  rw [stepEq, baseEq]

-- R1: applying the (unused) type argument discards the A-binder, leaving the two-argument iterator.
theorem churchNumeral_substType (depth : Nat) (typeA : RawTerm 0) :
    RawTerm.subst0
        (lamCell (lamCell (iteratedApplication depth
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
          (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))) ) typeA
      = lamCell (lamCell (iteratedApplication depth
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
          (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))) := by
  unfold RawTerm.subst0
  show lamCell (lamCell (RawTerm.subst
      (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.singleton typeA)))
      (iteratedApplication depth _ _))) = _
  rw [subst_iteratedApplication]
  rfl

-- R2: applying the step argument substitutes it for `f`, leaving the one-argument iterator.
theorem churchNumeral_substStep (depth : Nat) (handlerF : RawTerm 0) :
    RawTerm.subst0
        (lamCell (iteratedApplication depth
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
          (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))) handlerF
      = lamCell (iteratedApplication depth (RawTerm.weaken handlerF)
          (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) := by
  unfold RawTerm.subst0
  show lamCell (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton handlerF))
      (iteratedApplication depth _ _)) = _
  rw [subst_iteratedApplication]
  rfl

-- ★ The general iteration computation: churchNumeralLambda n applied to (A, f, x) reduces to f^n x.
theorem churchNumeral_appliedReducesToIterate_general (depth : Nat) (typeA handlerF baseX : RawTerm 0) :
    StepStar
      (appCell (appCell (appCell (churchNumeralLambda depth) typeA) handlerF) baseX)
      (iteratedApplication depth handlerF baseX) := by
  have step1 : Step (appCell (churchNumeralLambda depth) typeA)
      (lamCell (lamCell (iteratedApplication depth
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
        (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))) := by
    rw [← churchNumeral_substType depth typeA]; exact Step.beta
  have step2 : Step (appCell (lamCell (lamCell (iteratedApplication depth
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
        (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))) handlerF)
      (lamCell (iteratedApplication depth (RawTerm.weaken handlerF)
        (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) := by
    rw [← churchNumeral_substStep depth handlerF]; exact Step.beta
  have step3 : Step (appCell (lamCell (iteratedApplication depth (RawTerm.weaken handlerF)
        (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) baseX)
      (iteratedApplication depth handlerF baseX) := by
    rw [← iteratedApplication_subst0_weaken_step depth handlerF baseX]; exact Step.beta
  exact StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons baseX .childNil)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            (.childCons handlerF .childNil) step1))))
    (StepStar.trans
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
          (.childCons baseX .childNil) step2))
      (StepStar.trans step3 (StepStar.refl _)))

end FX1Poly.Typed

#print axioms FX1Poly.Typed.iteratedApplication_subst0_weaken_step
#print axioms FX1Poly.Typed.churchNumeral_substType
#print axioms FX1Poly.Typed.churchNumeral_substStep
#print axioms FX1Poly.Typed.churchNumeral_appliedReducesToIterate_general
