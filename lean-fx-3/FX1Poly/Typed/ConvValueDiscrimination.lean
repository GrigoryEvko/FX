import FX1Poly.Core.ConvNormalForm
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.ReducibilityCandidateArrow

/-! # Foundation/PolyCell/Typed/ConvValueDiscrimination
    — definitional equality discriminates distinct closed values (Conv non-degeneracy)

`ConvNormalForm.lean` proves the seed `Conv.eq_of_noStep`: when both endpoints
have no outgoing `Step`, conversion collapses to plain equality.  This file
draws the CONTRAPOSITIVE consequence — the *discrimination* power that makes the
conversion relation usable: two distinct closed normal-form values are NOT
convertible.

Concretely, `boolTrue` and `boolFalse` are not convertible, and neither are
`boolTrue` and `unit`.  The headline `convIsNonDegenerate` records the
consequence: there exist closed terms that are not convertible at all.  This is
a sanity property the whole type theory rests on — were every pair convertible,
`Conv` would identify every type, every type would be inhabited, and the theory
would be inconsistent (it is exactly the value-level discrimination canonicity
needs: the kernel can tell `true` from `false`).

The argument is uniform: `normalLeavesNotConvertibleOfDistinctRoot` takes two
no-step hypotheses and a proof that the head generators differ.  `Conv` on
no-step endpoints is `Eq` (`Conv.eq_of_noStep`); equal terms have equal root
generators (`congrArg RawTerm.rootGenerator`); so distinct roots refute
convertibility.  This is distinct from the Conv-INJECTIVITY of the type-code
formers (which decomposes `Conv (formerCell …) (formerCell …)` into
component-wise conversion) — here the two terms have DIFFERENT heads, so they do
not convert at all.

And the constructive companion — `Conv` on the normal fragment is DECIDABLE, and
the decider executes:

  * `convDecidableOfBothNoStep` — `Conv` on two no-step endpoints collapses to
    `Eq` (`Conv.iff_eq_of_noStep`), which the propext-free
    `DecidableEq (RawTerm scope)` decides, no normalizer required — fulfilling
    the decidable-`Conv` seed the `ConvNormalForm` docstring promises.
  * `convDecider_*` — the decider RUNS (the `@decide … = true / false` equations
    hold by `rfl`): it decides `Conv boolTrue boolTrue` to `true`, and
    `Conv boolTrue boolFalse` / `Conv boolTrue unit` to `false`.  The decision
    procedure is not merely a `Prop` but computes the right boolean.

Everything is about the raw `Conv` (= `StepStar.Join`); no typing derivation is
consulted.  Zero-axiom: the only non-`rfl` steps are `Conv.eq_of_noStep` and
`Generator.noConfusion` on the distinct head generators; the decider evaluations
are `rfl` over the structural `DecidableEq` (no `native_decide`).
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- The `boolTrue` value leaf. -/
def boolTrueValue : RawTerm 0 := .mkGen .gen_boolTrue () .childNil

/-- The `boolFalse` value leaf. -/
def boolFalseValue : RawTerm 0 := .mkGen .gen_boolFalse () .childNil

/-- The `unit` value leaf. -/
def unitValue : RawTerm 0 := .mkGen .gen_unit () .childNil

/-- Two normal-form (no outgoing `Step`) terms whose head generators differ are
NOT convertible.  `Conv` on no-step endpoints collapses to `Eq`
(`Conv.eq_of_noStep`), and equal terms have equal root generators, so distinct
roots refute convertibility. -/
theorem normalLeavesNotConvertibleOfDistinctRoot {scope : Nat}
    {leftTerm rightTerm : RawTerm scope}
    (leftHasNoStep : ∀ reduct : RawTerm scope, Step leftTerm reduct → False)
    (rightHasNoStep : ∀ reduct : RawTerm scope, Step rightTerm reduct → False)
    (rootsDiffer : RawTerm.rootGenerator leftTerm ≠ RawTerm.rootGenerator rightTerm) :
    ¬ Conv leftTerm rightTerm :=
  fun convertibility =>
    rootsDiffer (congrArg RawTerm.rootGenerator
      (Conv.eq_of_noStep leftHasNoStep rightHasNoStep convertibility))

/-- `boolTrue` and `boolFalse` are NOT convertible — the kernel distinguishes the
two boolean values. -/
theorem boolTrueValue_notConvertible_boolFalseValue :
    ¬ Conv boolTrueValue boolFalseValue :=
  normalLeavesNotConvertibleOfDistinctRoot
    (fun _ step => noStep_boolTrue step)
    (fun _ step => noStep_boolFalse step)
    (fun rootEq => Generator.noConfusion rootEq)

/-- `boolTrue` and `unit` are NOT convertible — distinct data values across types
do not convert. -/
theorem boolTrueValue_notConvertible_unitValue :
    ¬ Conv boolTrueValue unitValue :=
  normalLeavesNotConvertibleOfDistinctRoot
    (fun _ step => noStep_boolTrue step)
    (fun _ step => noStep_unit step)
    (fun rootEq => Generator.noConfusion rootEq)

/-- ★ Conversion is non-degenerate: there exist closed terms that are NOT
convertible.  Were every pair convertible, `Conv` would identify every type,
every type would be inhabited, and the theory would be inconsistent — so this
witnesses that definitional equality genuinely discriminates closed values, the
value-level sanity property canonicity rests on. -/
theorem convIsNonDegenerate :
    ∃ leftTerm rightTerm : RawTerm 0, ¬ Conv leftTerm rightTerm :=
  ⟨boolTrueValue, boolFalseValue, boolTrueValue_notConvertible_boolFalseValue⟩

/-- `Conv` on two no-step (normal) endpoints is decidable WITHOUT a normalizer:
it collapses to `Eq` (`Conv.iff_eq_of_noStep`), which the propext-free
`DecidableEq (RawTerm scope)` decides.  This is the decidable-`Conv` seed the
`ConvNormalForm` docstring promises, packaged as an actual `Decidable`. -/
def convDecidableOfBothNoStep {scope : Nat} {leftTerm rightTerm : RawTerm scope}
    (leftHasNoStep : ∀ reduct : RawTerm scope, Step leftTerm reduct → False)
    (rightHasNoStep : ∀ reduct : RawTerm scope, Step rightTerm reduct → False) :
    Decidable (Conv leftTerm rightTerm) :=
  decidable_of_iff (leftTerm = rightTerm)
    (Conv.iff_eq_of_noStep leftHasNoStep rightHasNoStep).symm

/-- The decider RUNS: it decides `Conv boolTrue boolTrue` to `true` (by `rfl`
over the structural `DecidableEq`). -/
theorem convDecider_boolTrueValue_self_isTrue :
    @decide (Conv boolTrueValue boolTrueValue)
      (convDecidableOfBothNoStep
        (fun _ step => noStep_boolTrue step) (fun _ step => noStep_boolTrue step)) = true :=
  rfl

/-- The decider RUNS: it decides `Conv boolTrue boolFalse` to `false`. -/
theorem convDecider_boolTrueValue_boolFalseValue_isFalse :
    @decide (Conv boolTrueValue boolFalseValue)
      (convDecidableOfBothNoStep
        (fun _ step => noStep_boolTrue step) (fun _ step => noStep_boolFalse step)) = false :=
  rfl

/-- The decider RUNS: it decides `Conv boolTrue unit` to `false`. -/
theorem convDecider_boolTrueValue_unitValue_isFalse :
    @decide (Conv boolTrueValue unitValue)
      (convDecidableOfBothNoStep
        (fun _ step => noStep_boolTrue step) (fun _ step => noStep_unit step)) = false :=
  rfl

end FX1Poly.Typed
