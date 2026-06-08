import FX1Poly.Typed.TypedChurchNumeralTyping

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

theorem subst_iteratedApplication {scopeSource scopeTarget : Nat}
    (sigma : RawTermSubst scopeSource scopeTarget) (n : Nat) (stepFn base : RawTerm scopeSource) :
    RawTerm.subst sigma (iteratedApplication n stepFn base)
      = iteratedApplication n (RawTerm.subst sigma stepFn) (RawTerm.subst sigma base) := by
  induction n with
  | zero => rfl
  | succ priorDepth priorIH =>
      show RawTerm.subst sigma (appCell stepFn (iteratedApplication priorDepth stepFn base))
        = appCell (RawTerm.subst sigma stepFn)
            (iteratedApplication priorDepth (RawTerm.subst sigma stepFn) (RawTerm.subst sigma base))
      have distributeEq : RawTerm.subst sigma (appCell stepFn (iteratedApplication priorDepth stepFn base))
          = appCell (RawTerm.subst sigma stepFn)
              (RawTerm.subst sigma (iteratedApplication priorDepth stepFn base)) := rfl
      rw [distributeEq, priorIH]

theorem churchNatType_hasInfinitelyManyDistinctInhabitants {profile : PolyProfile} (flag : UniverseFlag) :
    ∃ inhabitants : Nat → RawTerm 0,
      (∀ depthLeft depthRight, inhabitants depthLeft = inhabitants depthRight → depthLeft = depthRight)
      ∧ (∀ depth, HasTypeDescPi profile TypingContext.empty (inhabitants depth)
          (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
            (piTyCodeCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
                (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
              (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
                (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))))
      ∧ (∀ depthLeft depthRight, depthLeft ≠ depthRight
          → ¬ Conv (inhabitants depthLeft) (inhabitants depthRight)) :=
  ⟨churchNumeralLambda,
    fun _ _ sameNumeral => churchNumeralLambda_injective sameNumeral,
    fun depth => churchNumeralLambda_hasTypeDescPi flag depth,
    fun _ _ depthsDiffer => churchNumeralLambda_notConvertible_of_ne depthsDiffer⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.subst_iteratedApplication
#print axioms FX1Poly.Typed.churchNatType_hasInfinitelyManyDistinctInhabitants
