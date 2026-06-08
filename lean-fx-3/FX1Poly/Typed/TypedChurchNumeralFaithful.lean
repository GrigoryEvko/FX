import FX1Poly.Typed.TypedChurchNumeralThree
import FX1Poly.Core.RawSize

/-! # FX1Poly/Typed/TypedChurchNumeralFaithful — ℕ injects into the term model via the Church encoding

`TypedChurchNumeralDiscrimination.lean` and `TypedChurchNumeralThree.lean` proved the CONCRETE samples
`churchOne ≢ churchTwo` and the `{1,2,3}` antichain.  This file proves the GENERAL faithfulness — the capstone
of the Church arc:

  **`churchNumeralLambda_notConvertible_of_ne` (★)** — for ALL `m ≠ n`, the Church numerals `m` and `n` are
  NON-CONVERTIBLE.  The Church encoding of ℕ injects into the FX term model up to definitional equality.

The proof is uniform in `n` (no per-numeral case work) and avoids the de-Bruijn-payload `decide` and the
`childCons`-injection drilling, routing entirely through the structural SIZE measure:

  * `iteratedApplication n stepFn base = stepFn (stepFn (... (stepFn base)))` (`n` applications), and the general
    numeral `churchNumeralLambda n = λA.λf.λx. iteratedApplication n f x = λA.λf.λx. f^n x`.
  * `iteratedApplication_isStepNormalForm` — when the step is not a lambda (so a step-headed application is never
    a β-redex, `hasAppBetaRoot = isLamSource = false`) and both step and base are normal, the iterate is a
    no-step normal form (induction on `n`; the `appCell` normality equation is `rfl`).  Hence
    `churchNumeralLambda_isStepNormalForm` — every Church numeral is a closed normal form.
  * `iteratedApplication_size_var` — `size (iteratedApplication n (var)(var)) = 4·n + 1` (each application adds
    four nodes), so `churchNumeralLambda_size` — `size (churchNumeralLambda n) = 4·n + 7`.
  * `churchNumeralLambda_injective` — `size` is injective on the numerals (`congrArg size` then a `propext`-free
    `Nat.succ.inj` ×7 to strip the `+7` and `Nat.eq_of_mul_eq_mul_left` to strip the `·4`), so distinct depths
    give distinct numerals.
  * The headline then follows: both numerals are no-step normal forms, so `Conv.iff_eq_of_noStep` collapses any
    convertibility to syntactic equality, which `churchNumeralLambda_injective` refutes for `m ≠ n`.

`churchNumeralLambda 1 / 2 / 3` are DEFINITIONALLY `churchOneLambda / churchTwoLambda / churchThreeLambda`
(`churchNumeralLambda_one_eq` etc., `rfl`), so the general theorem SUBSUMES the concrete `{1,2,3}` antichain —
`churchNumerals_pairwiseNotConvertible_general` re-derives any pairwise non-convertibility as a specialization.

Zero-axiom: the `appCell`/`lamCell`/`variableCell` size and normal-form equations are `rfl`; the size induction
uses `Nat.mul_succ` + `Nat.add_comm`; the injectivity uses `Nat.succ.inj` + `Nat.eq_of_mul_eq_mul_left` (both
`propext`-free — `Nat.add_right_cancel` was avoided because it leaks `propext`); the headline reuses
`Conv.iff_eq_of_noStep` + `RawTerm.isStepNormalForm_blocks_step`.  No `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, or `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- `iteratedApplication n stepFn base` = `stepFn` applied `n` times to `base` —
`stepFn (stepFn (... (stepFn base)))`. -/
def iteratedApplication {scope : Nat} : Nat → RawTerm scope → RawTerm scope → RawTerm scope
  | 0, _stepFn, base => base
  | (depth + 1), stepFn, base => appCell stepFn (iteratedApplication depth stepFn base)

/-- When the step function is not a lambda (so a step-headed application is never a β-redex) and both step and
base are normal, the iterate is a no-step normal form.  Induction on `n`; the `appCell` normality equation
`isStepNormalFormBool (appCell f a) = (!isLamSource f && (… && (… && true)))` is `rfl`. -/
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

/-- `size (iteratedApplication n (var)(var)) = 4·n + 1` — each application adds four structural nodes
(one `app` node + the step variable + the two `childCons` cells). -/
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

/-- The general Church numeral `n = λ(A:Type@0). λ(f:A→A). λ(x:A). f^n x` — the polymorphic iterator applying
its step `f` exactly `n` times to its base `x`. -/
def churchNumeralLambda (depth : Nat) : RawTerm 0 :=
  lamCell (lamCell (lamCell
    (iteratedApplication depth
      (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
      (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))

/-- A lambda is a no-step normal form whenever its body is (the `lamCell` normality equation is `rfl`). -/
theorem lamCell_isStepNormalForm {scope : Nat} {body : RawTerm (scope + 1)}
    (bodyNormal : RawTerm.isStepNormalForm body) :
    RawTerm.isStepNormalForm (lamCell body) := by
  show RawTerm.isStepNormalFormBool (lamCell body) = true
  have nfEq : RawTerm.isStepNormalFormBool (lamCell body)
      = (!false && (RawTerm.isStepNormalFormBool body && true)) := rfl
  rw [nfEq, (bodyNormal : RawTerm.isStepNormalFormBool body = true)]
  decide

/-- Every Church numeral is a closed no-step normal form — three `lamCell` wrappers over the iterate, whose step
`f` (`var 1`) is a variable (not a lambda) and whose base `x` (`var 0`) is a variable. -/
theorem churchNumeralLambda_isStepNormalForm (depth : Nat) :
    RawTerm.isStepNormalForm (churchNumeralLambda depth) :=
  lamCell_isStepNormalForm (lamCell_isStepNormalForm (lamCell_isStepNormalForm
    (iteratedApplication_isStepNormalForm depth rfl (by decide) (by decide))))

/-- `size (churchNumeralLambda n) = 4·n + 7` — the iterate's `4·n + 1` plus the three `lamCell` wrappers
(`+2` each). -/
theorem churchNumeralLambda_size (depth : Nat) :
    (churchNumeralLambda depth).size = 4 * depth + 7 := by
  show (((iteratedApplication depth
    (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
    (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))).size + 2) + 2 + 2) = 4 * depth + 7
  rw [iteratedApplication_size_var]

/-- The Church numeral construction is injective: distinct depths give distinct (closed) numeral terms.  Via the
size `4·n + 7`, with a `propext`-free cancellation (`Nat.succ.inj` ×7 strips the `+7`, then
`Nat.eq_of_mul_eq_mul_left` strips the `·4`). -/
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

/-- ★ **The Church encoding of ℕ injects into the FX term model up to definitional equality.**  For all
`m ≠ n`, the Church numerals `m` and `n` are NON-CONVERTIBLE: both are closed no-step normal forms, so
`Conv.iff_eq_of_noStep` collapses any convertibility to syntactic equality, which `churchNumeralLambda_injective`
refutes.  The general faithfulness — the capstone of the Church-encoding arc (CHURCH-BOOL/NAT/DISCRIM/3). -/
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

/-! ## The general construction subsumes the concrete numerals -/

/-- `churchNumeralLambda 1` is definitionally `churchOneLambda`. -/
theorem churchNumeralLambda_one_eq : churchNumeralLambda 1 = churchOneLambda := rfl

/-- `churchNumeralLambda 2` is definitionally `churchTwoLambda`. -/
theorem churchNumeralLambda_two_eq : churchNumeralLambda 2 = churchTwoLambda := rfl

/-- `churchNumeralLambda 3` is definitionally `churchThreeLambda`. -/
theorem churchNumeralLambda_three_eq : churchNumeralLambda 3 = churchThreeLambda := rfl

/-- The concrete `{1,2,3}` antichain (CHURCH-NAT-3) re-derived as a specialization of the general faithfulness —
the general theorem subsumes the concrete samples. -/
theorem churchNumerals_pairwiseNotConvertible_general :
    (¬ Conv (churchNumeralLambda 1) (churchNumeralLambda 2))
    ∧ (¬ Conv (churchNumeralLambda 1) (churchNumeralLambda 3))
    ∧ (¬ Conv (churchNumeralLambda 2) (churchNumeralLambda 3)) :=
  ⟨churchNumeralLambda_notConvertible_of_ne (by decide),
    churchNumeralLambda_notConvertible_of_ne (by decide),
    churchNumeralLambda_notConvertible_of_ne (by decide)⟩

end FX1Poly.Typed
