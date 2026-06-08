import FX1Poly.Typed.TypedChurchNumeralIteration
import FX1Poly.Core.ConvCongruence

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- The bare Church-`one` lambda `λA.λf.λx. f x`. -/
abbrev churchOneLambda : RawTerm 0 :=
  lamCell (lamCell (lamCell
    (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
      (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))

/-- The bare Church-`two` lambda `λA.λf.λx. f (f x)`. -/
abbrev churchTwoLambda : RawTerm 0 :=
  lamCell (lamCell (lamCell
    (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
      (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
        (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))))))

abbrev natTypeZeroCode : RawTerm 0 := universeCodeCell LevelExpr.lzero UniverseFlag.standard
abbrev natTypeOneCode : RawTerm 0 := universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard

/-- `one` applied to `Type@0/Type@0/Type@1` computes the once-iterate `f x = app(Type@0, Type@1)`. -/
abbrev churchOneIterate : RawTerm 0 := appCell natTypeZeroCode natTypeOneCode

/-- `two` applied to the same inputs computes `f (f x) = app(Type@0, app(Type@0, Type@1))`. -/
abbrev churchTwoIterate : RawTerm 0 := appCell natTypeZeroCode (appCell natTypeZeroCode natTypeOneCode)

theorem churchOneIterate_isStepNormalForm : RawTerm.isStepNormalForm churchOneIterate := by decide
theorem churchTwoIterate_isStepNormalForm : RawTerm.isStepNormalForm churchTwoIterate := by decide

/-- The two iterates are NOT convertible: both are no-step normal forms, so `Conv` collapses to syntactic
equality, refuted by the structural `DecidableEq` (the difference is the second child — `Type@1` vs an
application — so `decide` never compares de Bruijn indices). -/
theorem churchOneIterate_notConvertible_churchTwoIterate : ¬ Conv churchOneIterate churchTwoIterate :=
  fun convertibility =>
    absurd
      ((Conv.iff_eq_of_noStep
          (fun reduct step =>
            RawTerm.isStepNormalForm_blocks_step churchOneIterate_isStepNormalForm reduct step)
          (fun reduct step =>
            RawTerm.isStepNormalForm_blocks_step churchTwoIterate_isStepNormalForm reduct step)).mp
        convertibility)
      (by decide)

/-- ★ `churchOne` and `churchTwo` are NOT convertible — the Church numeral encoding faithfully distinguishes 1
from 2.  Through their COMPUTATION (not a de Bruijn payload inspection): applied to `Type@0/Type@0/Type@1` they
reduce to the distinct iterates `f x` vs `f (f x)`, so a hypothetical `churchOne ≡ churchTwo` would — by three
layers of application congruence plus the two iteration reductions — force the non-convertible iterates equal. -/
theorem churchOne_notConvertible_churchTwo : ¬ Conv churchOneLambda churchTwoLambda := by
  intro convNumerals
  have convApplied :
      Conv (appCell (appCell (appCell churchOneLambda natTypeZeroCode) natTypeZeroCode) natTypeOneCode)
           (appCell (appCell (appCell churchTwoLambda natTypeZeroCode) natTypeZeroCode) natTypeOneCode) :=
    Conv.app_cong
      (Conv.app_cong (Conv.app_cong convNumerals (Conv.refl _)) (Conv.refl _))
      (Conv.refl _)
  have convIterates : Conv churchOneIterate churchTwoIterate :=
    Conv.trans
      (Conv.sym (Conv.fromStepStar (churchOne_appliedReducesToIterate UniverseFlag.standard)))
      (Conv.trans convApplied
        (Conv.fromStepStar (churchTwo_appliedReducesToIterate UniverseFlag.standard)))
  exact churchOneIterate_notConvertible_churchTwoIterate convIterates

end FX1Poly.Typed

#print axioms FX1Poly.Typed.churchOneIterate_notConvertible_churchTwoIterate
#print axioms FX1Poly.Typed.churchOne_notConvertible_churchTwo
