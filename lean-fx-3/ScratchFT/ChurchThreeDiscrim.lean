import FX1Poly.Typed.TypedChurchNumeralDiscrimination

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

abbrev churchThreeLambda : RawTerm 0 :=
  lamCell (lamCell (lamCell
    (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
      (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
        (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
          (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))))

/-- `f (f (f x))` at the iteration fixtures. -/
abbrev churchThreeIterate : RawTerm 0 :=
  appCell numeralTypeZeroCode (appCell numeralTypeZeroCode (appCell numeralTypeZeroCode numeralTypeOneCode))

theorem churchThreeIterate_isStepNormalForm : RawTerm.isStepNormalForm churchThreeIterate := by decide

/-- `three A f x` β-reduces (three steps) to `f (f (f x))`. -/
theorem churchThree_appliedReducesToIterate (flag : UniverseFlag) :
    StepStar
      (appCell (appCell (appCell churchThreeLambda
          (universeCodeCell LevelExpr.lzero flag))
          (universeCodeCell LevelExpr.lzero flag))
        (universeCodeCell LevelExpr.lzero.lsucc flag))
      (appCell (universeCodeCell LevelExpr.lzero flag)
        (appCell (universeCodeCell LevelExpr.lzero flag)
          (appCell (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero.lsucc flag)))) :=
  StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        ((.childCons (universeCodeCell LevelExpr.lzero.lsucc flag) .childNil) : RawTermChildren [0] 0)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            ((.childCons (universeCodeCell LevelExpr.lzero flag) .childNil) : RawTermChildren [0] 0)
            Step.beta))))
    (StepStar.trans
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
          ((.childCons (universeCodeCell LevelExpr.lzero.lsucc flag) .childNil) : RawTermChildren [0] 0)
          Step.beta))
      (StepStar.trans Step.beta (StepStar.refl _)))

theorem churchOneIterate_notConvertible_churchThreeIterate : ¬ Conv churchOneIterate churchThreeIterate :=
  fun convertibility =>
    absurd
      ((Conv.iff_eq_of_noStep
          (fun reduct step =>
            RawTerm.isStepNormalForm_blocks_step churchOneIterate_isStepNormalForm reduct step)
          (fun reduct step =>
            RawTerm.isStepNormalForm_blocks_step churchThreeIterate_isStepNormalForm reduct step)).mp
        convertibility)
      (by decide)

theorem churchTwoIterate_notConvertible_churchThreeIterate : ¬ Conv churchTwoIterate churchThreeIterate :=
  fun convertibility =>
    absurd
      ((Conv.iff_eq_of_noStep
          (fun reduct step =>
            RawTerm.isStepNormalForm_blocks_step churchTwoIterate_isStepNormalForm reduct step)
          (fun reduct step =>
            RawTerm.isStepNormalForm_blocks_step churchThreeIterate_isStepNormalForm reduct step)).mp
        convertibility)
      (by decide)

theorem churchOne_notConvertible_churchThree : ¬ Conv churchOneLambda churchThreeLambda := by
  intro convNumerals
  have convApplied :
      Conv (appCell (appCell (appCell churchOneLambda numeralTypeZeroCode) numeralTypeZeroCode) numeralTypeOneCode)
           (appCell (appCell (appCell churchThreeLambda numeralTypeZeroCode) numeralTypeZeroCode) numeralTypeOneCode) :=
    Conv.app_cong (Conv.app_cong (Conv.app_cong convNumerals (Conv.refl _)) (Conv.refl _)) (Conv.refl _)
  have convIterates : Conv churchOneIterate churchThreeIterate :=
    Conv.trans
      (Conv.sym (Conv.fromStepStar (churchOne_appliedReducesToIterate UniverseFlag.standard)))
      (Conv.trans convApplied
        (Conv.fromStepStar (churchThree_appliedReducesToIterate UniverseFlag.standard)))
  exact churchOneIterate_notConvertible_churchThreeIterate convIterates

theorem churchTwo_notConvertible_churchThree : ¬ Conv churchTwoLambda churchThreeLambda := by
  intro convNumerals
  have convApplied :
      Conv (appCell (appCell (appCell churchTwoLambda numeralTypeZeroCode) numeralTypeZeroCode) numeralTypeOneCode)
           (appCell (appCell (appCell churchThreeLambda numeralTypeZeroCode) numeralTypeZeroCode) numeralTypeOneCode) :=
    Conv.app_cong (Conv.app_cong (Conv.app_cong convNumerals (Conv.refl _)) (Conv.refl _)) (Conv.refl _)
  have convIterates : Conv churchTwoIterate churchThreeIterate :=
    Conv.trans
      (Conv.sym (Conv.fromStepStar (churchTwo_appliedReducesToIterate UniverseFlag.standard)))
      (Conv.trans convApplied
        (Conv.fromStepStar (churchThree_appliedReducesToIterate UniverseFlag.standard)))
  exact churchTwoIterate_notConvertible_churchThreeIterate convIterates

/-- ★ The three Church numerals form a pairwise-non-convertible 3-antichain under definitional equality. -/
theorem churchNumerals_oneTwoThree_pairwiseNotConvertible :
    (¬ Conv churchOneLambda churchTwoLambda)
    ∧ (¬ Conv churchOneLambda churchThreeLambda)
    ∧ (¬ Conv churchTwoLambda churchThreeLambda) :=
  ⟨churchOne_notConvertible_churchTwo,
    churchOne_notConvertible_churchThree,
    churchTwo_notConvertible_churchThree⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.churchThree_appliedReducesToIterate
#print axioms FX1Poly.Typed.churchOne_notConvertible_churchThree
#print axioms FX1Poly.Typed.churchTwo_notConvertible_churchThree
#print axioms FX1Poly.Typed.churchNumerals_oneTwoThree_pairwiseNotConvertible
