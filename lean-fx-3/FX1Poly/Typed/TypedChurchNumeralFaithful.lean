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
      rfl

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

/-- The universe-code domain of the Church numeral's type binder `A:Type@0` (at the empty scope).  Under T2 the
outer `lamCell` carries this domain; it is the `domainCode` the numeral's `piIntro` typing rule names
(`churchNumeralLambda_hasTypeDescPi`).  Pinned to the `standard` flag so the numeral term keeps its fixed
`RawTerm 0` arity across every call site; the typed derivation instantiates the Church Nat type at this flag. -/
def churchNumeralTypeBinderDomain : RawTerm 0 :=
  universeCodeCell LevelExpr.lzero UniverseFlag.standard

/-- The arrow domain `A→A` of the Church numeral's step binder `f:A→A` (under the `A` binder, scope 1).  Under
T2 the middle `lamCell` carries this domain — the `churchNatArrow` subject. -/
def churchNumeralStepBinderDomain : RawTerm 1 :=
  piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
    (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))

/-- The type-variable domain `A` of the Church numeral's base binder `x:A` (under the `A`,`f` binders, scope 2,
de Bruijn `var 1`).  Under T2 the inner `lamCell` carries this domain. -/
def churchNumeralBaseBinderDomain : RawTerm 2 :=
  variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)

/-- The general Church numeral `n = λ(A:Type@0). λ(f:A→A). λ(x:A). f^n x` — the polymorphic iterator applying
its step `f` exactly `n` times to its base `x`.  Under T2 each binder carries its domain annotation (the
universe code, the arrow `A→A`, the type variable `A`), exactly the domains the `piIntro` typing rule names. -/
def churchNumeralLambda (depth : Nat) : RawTerm 0 :=
  lamCell churchNumeralTypeBinderDomain
    (lamCell churchNumeralStepBinderDomain
      (lamCell churchNumeralBaseBinderDomain
        (iteratedApplication depth
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
          (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))

/-- A lambda is a no-step normal form whenever BOTH its domain annotation and its body are (the `lamCell`
normality equation — over the two-child Church-style telescope — is `rfl`). -/
theorem lamCell_isStepNormalForm {scope : Nat} {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    (domainNormal : RawTerm.isStepNormalForm domainAnn)
    (bodyNormal : RawTerm.isStepNormalForm body) :
    RawTerm.isStepNormalForm (lamCell domainAnn body) := by
  show RawTerm.isStepNormalFormBool (lamCell domainAnn body) = true
  have nfEq : RawTerm.isStepNormalFormBool (lamCell domainAnn body)
      = (!false && (RawTerm.isStepNormalFormBool domainAnn
          && (RawTerm.isStepNormalFormBool body && true))) := rfl
  rw [nfEq, (domainNormal : RawTerm.isStepNormalFormBool domainAnn = true),
    (bodyNormal : RawTerm.isStepNormalFormBool body = true)]
  rfl

/-- Every Church numeral is a closed no-step normal form — three `lamCell` wrappers over the iterate, whose step
`f` (`var 1`) is a variable (not a lambda) and whose base `x` (`var 0`) is a variable. -/
theorem churchNumeralLambda_isStepNormalForm (depth : Nat) :
    RawTerm.isStepNormalForm (churchNumeralLambda depth) :=
  lamCell_isStepNormalForm rfl
    (lamCell_isStepNormalForm rfl
      (lamCell_isStepNormalForm rfl
        (iteratedApplication_isStepNormalForm depth rfl rfl rfl)))

/-- **The three-wrapper size offset, propext-free.**  The constant-gathering identity the Church-numeral
size proof reduces to once the iterate's size `iterateCount` is generalised: the three `lamCell` wrappers'
domain/body/`+3` contributions sum the `iterateCount` plus a constant `+17`.  Proved by structural
recursion on `iterateCount` (the successor case is `Nat.succ` congruence, the base case `rfl`) — no
`Nat.add_mul`, no `ac_rfl`, no `omega`. -/
theorem wrapperSizeOffset (iterateCount : Nat) :
    1 + (5 + (1 + (iterateCount + 1) + 3) + 3) + 3 = iterateCount + 17 := by
  induction iterateCount with
  | zero => rfl
  | succ priorCount priorEquation =>
      show Nat.succ (1 + (5 + (1 + (priorCount + 1) + 3) + 3) + 3) = Nat.succ (priorCount + 17)
      exact congrArg Nat.succ priorEquation

/-- `size (churchNumeralLambda n) = 4·n + 17` — the iterate's `4·n + 1` plus the three annotated `lamCell`
wrappers.  Under T2 each `lamCell` carries a domain child, so a wrapper adds `domain.size + body.size + 3`:
the base binder's type-variable domain (`+1`) gives `+4`, the step binder's arrow domain `A→A` (`+5`) gives
`+12`, the type binder's universe-code domain (`+1`) gives `+16` — `4·n + 1 + 16`. -/
theorem churchNumeralLambda_size (depth : Nat) :
    (churchNumeralLambda depth).size = 4 * depth + 17 := by
  have iterateSize :
      (iteratedApplication depth
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
        (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))).size = 4 * depth + 1 :=
    iteratedApplication_size_var depth _ _
  rw [churchNumeralLambda]
  show ((lamCell (churchNumeralTypeBinderDomain)
      (lamCell (churchNumeralStepBinderDomain)
        (lamCell (churchNumeralBaseBinderDomain)
          (iteratedApplication depth
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
            (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))).size) = 4 * depth + 17
  rw [show ∀ (domainAnn : RawTerm 0) (body : RawTerm 1),
        (lamCell domainAnn body).size = domainAnn.size + body.size + 3 from fun _ _ => rfl,
      show ∀ (domainAnn : RawTerm 1) (body : RawTerm 2),
        (lamCell domainAnn body).size = domainAnn.size + body.size + 3 from fun _ _ => rfl,
      show ∀ (domainAnn : RawTerm 2) (body : RawTerm 3),
        (lamCell domainAnn body).size = domainAnn.size + body.size + 3 from fun _ _ => rfl,
      iterateSize,
      show churchNumeralTypeBinderDomain.size = 1 from rfl,
      show churchNumeralStepBinderDomain.size = 5 from rfl,
      show churchNumeralBaseBinderDomain.size = 1 from rfl]
  show 1 + (5 + (1 + (4 * depth + 1) + 3) + 3) + 3 = 4 * depth + 17
  generalize 4 * depth = iterateCount
  exact wrapperSizeOffset iterateCount

/-- The Church numeral construction is injective: distinct depths give distinct (closed) numeral terms.  Via the
size `4·n + 17`, with a `propext`-free cancellation (`Nat.succ.inj` ×17 strips the `+17`, then
`Nat.eq_of_mul_eq_mul_left` strips the `·4`). -/
theorem churchNumeralLambda_injective {depthLeft depthRight : Nat}
    (sameNumeral : churchNumeralLambda depthLeft = churchNumeralLambda depthRight) :
    depthLeft = depthRight := by
  have sizeEq : (churchNumeralLambda depthLeft).size = (churchNumeralLambda depthRight).size :=
    congrArg RawTerm.size sameNumeral
  rw [churchNumeralLambda_size, churchNumeralLambda_size] at sizeEq
  have fourEq : 4 * depthLeft = 4 * depthRight :=
    Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
      (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
        (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
          (Nat.succ.inj (Nat.succ.inj sizeEq))))))))))))))))
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
