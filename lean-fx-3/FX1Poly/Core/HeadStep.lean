import FX1Poly.Core.RawTermSubst0

/-! # Foundation/PolyCell/Core/HeadStep
    — deterministic weak-head reduction for type-codes

A type-code reaches its head former by **weak-head reduction**: contract the head β-redex, or, when
the function position is not yet a λ, head-reduce inside the function.  `HeadStep` is exactly that
relation — β at the head plus congruence into the function child of an application — and nothing else
(no reduction inside arguments or under binders).

Its defining property is **determinism**: a term has at most one weak-head reduct (`HeadStep` is a
partial function).  Unlike full `Step`, this needs no confluence — the leftmost-outermost head redex
is unique.  This is the substrate a weak-head-normal dispatching reducibility interpretation needs to
stay conversion-invariant, and it is reusable for normalization by evaluation and decidable
conversion.

## Zero-axiom verification

A two-constructor inductive `Prop` + a `not_from_lam` inversion (a λ has no weak-head step) +
determinism by induction on the first step inverting the second.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Weak-head reduction.**  Contract the head β-redex (`beta`), or head-reduce inside the function
position of an application (`appCongruence`).  Deterministic by construction: at most one head redex
exists. -/
inductive HeadStep {scope : Nat} : RawTerm scope → RawTerm scope → Prop where
  /-- Head β-contraction: a λ applied to an argument steps to the substituted body. -/
  | beta {body : RawTerm (scope + 1)} {argument : RawTerm scope} :
      HeadStep
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons argument .childNil)))
        (RawTerm.subst0 body argument)
  /-- Head congruence: when the function position weak-head reduces, so does the application. -/
  | appCongruence {function functionReduct argument : RawTerm scope} :
      HeadStep function functionReduct →
      HeadStep
        (.mkGen .gen_app () (.childCons function (.childCons argument .childNil)))
        (.mkGen .gen_app () (.childCons functionReduct (.childCons argument .childNil)))

/-- A λ-abstraction has no weak-head step: both `HeadStep` constructors conclude an application-headed
subject, and `gen_lam ≠ gen_app`. -/
theorem HeadStep.not_from_lam {scope : Nat} {body : RawTerm (scope + 1)}
    {reduct : RawTerm scope} :
    ¬ HeadStep (.mkGen .gen_lam () (.childCons body .childNil)) reduct := by
  intro headStep
  cases headStep

/-- **Weak-head reduction is deterministic**: a term has at most one weak-head reduct.  Induction on
the first step, inverting the second.  In the β case the second step cannot be a head congruence (its
function premise would head-step a λ, refuted by `not_from_lam`); in the congruence case the second
step cannot be β (the function head-steps, so it is not a λ) and the congruence sub-case closes by the
induction hypothesis. -/
theorem HeadStep.deterministic {scope : Nat} {term firstReduct secondReduct : RawTerm scope}
    (firstStep : HeadStep term firstReduct) :
    HeadStep term secondReduct → firstReduct = secondReduct := by
  induction firstStep generalizing secondReduct with
  | beta =>
      intro secondStep
      cases secondStep with
      | beta => rfl
      | appCongruence functionStep => exact absurd functionStep HeadStep.not_from_lam
  | appCongruence functionStep functionInductiveHypothesis =>
      intro secondStep
      cases secondStep with
      | beta => exact absurd functionStep HeadStep.not_from_lam
      | appCongruence functionStep2 =>
          rw [functionInductiveHypothesis functionStep2]

end FX1Poly.Core
