import FX1Poly.Typed.TypedChurchNumeralThree
import FX1Poly.Core.RawSize

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

def iteratedApplication {scope : Nat} : Nat → RawTerm scope → RawTerm scope → RawTerm scope
  | 0, _stepFn, base => base
  | (depth + 1), stepFn, base => appCell stepFn (iteratedApplication depth stepFn base)

theorem iteratedApplication_isStepNormalForm {scope : Nat} (depth : Nat)
    {stepFn base : RawTerm scope}
    (stepNotLam : RawTerm.isLamSource stepFn = false)
    (stepNormal : RawTerm.isStepNormalForm stepFn)
    (baseNormal : RawTerm.isStepNormalForm base) :
    RawTerm.isStepNormalForm (iteratedApplication depth stepFn base) := by
  induction depth with
  | zero => exact baseNormal
  | succ priorDepth priorIH =>
      show RawTerm.isStepNormalFormBool (appCell stepFn (iteratedApplication priorDepth stepFn base)) = true
      have nfEq : RawTerm.isStepNormalFormBool (appCell stepFn (iteratedApplication priorDepth stepFn base))
          = (!RawTerm.isLamSource stepFn
              && (RawTerm.isStepNormalFormBool stepFn
                && (RawTerm.isStepNormalFormBool (iteratedApplication priorDepth stepFn base) && true))) := rfl
      rw [nfEq, stepNotLam, (stepNormal : RawTerm.isStepNormalFormBool stepFn = true),
        (priorIH : RawTerm.isStepNormalFormBool (iteratedApplication priorDepth stepFn base) = true)]
      decide

theorem iteratedApplication_size_var {scope : Nat} (depth : Nat)
    (stepIndex baseIndex : Fin scope) :
    (iteratedApplication depth (variableCell stepIndex) (variableCell baseIndex)).size
      = 4 * depth + 1 := by
  induction depth with
  | zero => rfl
  | succ priorDepth priorIH =>
      show (1
        + (iteratedApplication priorDepth (variableCell stepIndex) (variableCell baseIndex)).size + 3)
          = 4 * (priorDepth + 1) + 1
      rw [priorIH, Nat.mul_succ, Nat.add_comm 1 (4 * priorDepth + 1)]

/-- The general Church numeral `n = λA.λf.λx. f^n x`. -/
def churchNumeralLambda (depth : Nat) : RawTerm 0 :=
  lamCell (lamCell (lamCell
    (iteratedApplication depth
      (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
      (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))

theorem lamCell_isStepNormalForm {scope : Nat} {body : RawTerm (scope + 1)}
    (bodyNormal : RawTerm.isStepNormalForm body) :
    RawTerm.isStepNormalForm (lamCell body) := by
  show RawTerm.isStepNormalFormBool (lamCell body) = true
  have nfEq : RawTerm.isStepNormalFormBool (lamCell body)
      = (!false && (RawTerm.isStepNormalFormBool body && true)) := rfl
  rw [nfEq, (bodyNormal : RawTerm.isStepNormalFormBool body = true)]
  decide

theorem churchNumeralLambda_isStepNormalForm (depth : Nat) :
    RawTerm.isStepNormalForm (churchNumeralLambda depth) :=
  lamCell_isStepNormalForm (lamCell_isStepNormalForm (lamCell_isStepNormalForm
    (iteratedApplication_isStepNormalForm depth rfl (by decide) (by decide))))

theorem churchNumeralLambda_size (depth : Nat) :
    (churchNumeralLambda depth).size = 4 * depth + 7 := by
  show (((iteratedApplication depth
    (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
    (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))).size + 2) + 2 + 2) = 4 * depth + 7
  rw [iteratedApplication_size_var]

theorem churchNumeralLambda_injective {depthLeft depthRight : Nat}
    (sameNumeral : churchNumeralLambda depthLeft = churchNumeralLambda depthRight) :
    depthLeft = depthRight := by
  have sizeEq : (churchNumeralLambda depthLeft).size = (churchNumeralLambda depthRight).size :=
    congrArg RawTerm.size sameNumeral
  rw [churchNumeralLambda_size, churchNumeralLambda_size] at sizeEq
  have fourEq : 4 * depthLeft = 4 * depthRight :=
    Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
      (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj sizeEq))))))
  exact Nat.eq_of_mul_eq_mul_left (by decide) fourEq

/-- ★ The Church encoding of ℕ injects into the term model: distinct numerals are non-convertible. -/
theorem churchNumeralLambda_notConvertible_of_ne {depthLeft depthRight : Nat}
    (depthsDiffer : depthLeft ≠ depthRight) :
    ¬ Conv (churchNumeralLambda depthLeft) (churchNumeralLambda depthRight) := by
  intro convertibility
  have numeralsEqual : churchNumeralLambda depthLeft = churchNumeralLambda depthRight :=
    (Conv.iff_eq_of_noStep
      (fun reduct step =>
        RawTerm.isStepNormalForm_blocks_step (churchNumeralLambda_isStepNormalForm depthLeft) reduct step)
      (fun reduct step =>
        RawTerm.isStepNormalForm_blocks_step (churchNumeralLambda_isStepNormalForm depthRight) reduct step)).mp
      convertibility
  exact depthsDiffer (churchNumeralLambda_injective numeralsEqual)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.iteratedApplication_isStepNormalForm
#print axioms FX1Poly.Typed.iteratedApplication_size_var
#print axioms FX1Poly.Typed.churchNumeralLambda_isStepNormalForm
#print axioms FX1Poly.Typed.churchNumeralLambda_injective
#print axioms FX1Poly.Typed.churchNumeralLambda_notConvertible_of_ne
