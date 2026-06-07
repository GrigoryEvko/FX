import FX1Poly.Typed.ClosedSNSmoke

/-! # Foundation/PolyCell/Typed/StepNonDeterministic
    - single-step reduction is non-deterministic, yet the diamond closes

The raw confluence theorem (`#420`, the Takahashi/ParStep development) proves
Church-Rosser for `StepStar`: if `t →* a` and `t →* b` then `a` and `b` have a
common reduct.  This file exhibits the concrete reason that theorem is NOT
vacuous — single-step `Step` is genuinely NON-DETERMINISTIC.  A closed term can
have two DISTINCT one-step reducts, and confluence is exactly the non-trivial
fact that those divergences always reconverge.

Witness: `(λx. boolTrue) ((λy. y) unit)`, which has two redexes:

  * the **outer** redex fires the head application, discarding the argument and
    landing on `boolTrue` (a normal form);
  * the **inner** redex reduces the argument `(λy. y) unit` in place (the uniform
    congruence rule stepping the second child), landing on
    `(λx. boolTrue) unit`.

These two reducts are distinct — they differ at the root generator
(`gen_boolTrue` vs `gen_app`), refuted in one line by `Generator.noConfusion` on
`rootGenerator`.  So `Step` is non-deterministic.  Yet the diamond closes: the
outer reduct `boolTrue` is already normal, and the inner reduct
`(λx. boolTrue) unit` reduces in one further β-step to the SAME `boolTrue`.  This
is a concrete, hand-checkable instance of the local-confluence diamond that the
general Church-Rosser theorem generalizes.

Everything is about the raw `Step` / `StepStar` relations; no typing derivation
is consulted.  Both β reducts compute by `Step.beta` (the discarded body
`boolTrue` and the identity application's `subst0` reduce by definition — nullary
leaf / `var 0` substitution); the inner step uses the uniform `Step.cong` rule
with `StepChildren.there`.  Zero-axiom.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- The `boolTrue` value cell — a nullary normal-form leaf, scope-polymorphic. -/
def trueValueCell {scope : Nat} : RawTerm scope :=
  .mkGen .gen_boolTrue () .childNil

/-- `λx. boolTrue` — a constant function whose body discards the bound variable. -/
def constantTrueLambda : RawTerm 0 :=
  lamCell trueValueCell

/-- `(λy. y) unit` — an inner β-redex (the identity applied to `unit`). -/
def innerIdentityRedex : RawTerm 0 :=
  appCell (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) unitCell

/-- `(λx. boolTrue) ((λy. y) unit)` — a closed term carrying BOTH an outer redex
(the head application) and an inner redex (its argument). -/
def nondeterministicTerm : RawTerm 0 :=
  appCell constantTrueLambda innerIdentityRedex

/-- `(λx. boolTrue) unit` — the inner reduct (the argument reduced to `unit`). -/
def innerReduct : RawTerm 0 :=
  appCell constantTrueLambda unitCell

/-- **Outer reduction.**  The head redex fires, discarding the argument; the
reduct is the discarded body `boolTrue` (by `subst0` on a nullary leaf). -/
theorem nondeterministicTerm_outerStep :
    Step nondeterministicTerm trueValueCell :=
  Step.beta

/-- **Inner reduction.**  The argument redex `(λy. y) unit` fires under the
uniform congruence rule (stepping the second child of the application); the
reduct is `(λx. boolTrue) unit`. -/
theorem nondeterministicTerm_innerStep :
    Step nondeterministicTerm innerReduct := by
  apply Step.cong .gen_app ()
  apply StepChildren.there
  apply StepChildren.here
  exact Step.beta

/-- The two one-step reducts are DISTINCT: they differ at the root generator
(`gen_boolTrue` vs `gen_app`), so `Step` is non-deterministic. -/
theorem outerReduct_ne_innerReduct : (trueValueCell : RawTerm 0) ≠ innerReduct :=
  fun equalReducts => Generator.noConfusion (congrArg RawTerm.rootGenerator equalReducts)

/-- The outer reduct `boolTrue` is already a normal form — it reaches the common
reduct in zero steps. -/
theorem outerReduct_reachesCommon :
    StepStar (trueValueCell : RawTerm 0) trueValueCell :=
  StepStar.refl _

/-- The inner reduct `(λx. boolTrue) unit` reduces to the common reduct
`boolTrue` in one further β-step — the diamond closes. -/
theorem innerReduct_reachesCommon : StepStar innerReduct trueValueCell :=
  StepStar.single Step.beta

/-- ★ `Step` is non-deterministic, yet the diamond closes.  There is a closed
term with two DISTINCT one-step reducts that nonetheless reconverge to a common
reduct.  This is the concrete witness that raw confluence (`#420`,
Church-Rosser) is not vacuous: the single-step relation it tames genuinely
branches, and the content of the theorem is exactly that every such branch
rejoins. -/
theorem stepIsNonDeterministicButDiamondCloses :
    ∃ source firstReduct secondReduct commonReduct : RawTerm 0,
      Step source firstReduct ∧ Step source secondReduct ∧
      firstReduct ≠ secondReduct ∧
      StepStar firstReduct commonReduct ∧ StepStar secondReduct commonReduct :=
  ⟨nondeterministicTerm, trueValueCell, innerReduct, trueValueCell,
    nondeterministicTerm_outerStep, nondeterministicTerm_innerStep,
    outerReduct_ne_innerReduct, outerReduct_reachesCommon, innerReduct_reachesCommon⟩

end FX1Poly.Typed
