import FX1Poly.Typed.ClosedSNSmoke

/-! # Foundation/PolyCell/Typed/UntypedOmegaNotStronglyNormalizing
    - the SN-043 typing hypothesis is ESSENTIAL

The companion piece to the closed-SN smoke corpus (`ClosedSNSmoke.lean`).  The
closed smokes confirm that every *well-typed* closed term the formation/grown
engine accepts is `IsStronglyNormalizing`.  A natural skeptic's question is
whether typing is doing any work at all: maybe the raw reduction system is
already strongly normalizing on its own, so SN-043 (`HasTypeDescPi Γ t T →
IsStronglyNormalizing t`, the `#546` headline) would be vacuous.

It is not.  This file exhibits the prototypical counterexample — the Ω
combinator `(λx. x x) (λx. x x)` — as a *closed raw term* that is NOT strongly
normalizing: it β-reduces to itself, so it has an infinite reduction sequence.
Ω is untypable (self-application `x x` has no type in the engine), which is
exactly why SN-043 excludes it.  The headline
`applicationOfStronglyNormalizingNotAlwaysStronglyNormalizing` packages the
sharper fact: even the application of a strongly-normalizing function to a
strongly-normalizing argument can fail to be strongly normalizing
(`λx. x x` IS a normal form, yet applying it to itself diverges).  So the
β-redex side condition that the reducibility argument discharges is genuinely
load-bearing — strong normalization is not closed under application, and the
typing hypothesis in SN-043 is not decoration.

Everything here is about the *raw* `Step` relation; no typing derivation is
ever consulted.  The proofs use only the `Step` inversion lemmas
(`Step.from_lam`, `Step.from_app`), the normal-leaf no-step lemma
(`noStep_var`), and the accessibility endpoint `isStronglyNormalizing_of_noStep`,
all from the Core layer.  Zero-axiom.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- An element accessible under a relation cannot be related to itself: the
well-founded accessibility induction feeds the self-loop back into its own
induction hypothesis.  This is the kernel of "a self-looping element is not
`Acc`", proved propext-free by direct `Acc.rec` with a constant-in-proof
motive. -/
theorem accessibleElementNotSelfRelated {carrier : Type}
    {relation : carrier → carrier → Prop} {element : carrier}
    (accessible : Acc relation element) (selfRelated : relation element element) :
    False :=
  Acc.rec (motive := fun point _ => relation point point → False)
    (fun point _accessors inductiveHypothesis selfAtPoint =>
      inductiveHypothesis point selfAtPoint selfAtPoint)
    accessible selfRelated

/-- `λx. x x` — the self-application abstraction (Church-annotated with a cheap
closed domain `unit`; the annotation is discarded by β so divergence is
unchanged).  Its body applies the bound variable to itself; closed at scope `0`. -/
def selfApplicationLambda : RawTerm 0 :=
  lamCell (.mkGen .gen_unit () .childNil)
    (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
      (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))

/-- `Ω = (λx. x x) (λx. x x)` — the prototypical non-normalizing closed term. -/
def omegaCombinator : RawTerm 0 :=
  appCell selfApplicationLambda selfApplicationLambda

/-- Ω β-reduces to itself: `(λx. x x) (λx. x x) ↝ (x x)[x := λx. x x]`, and the
substitution computes definitionally back to Ω, so the reduct equals the source
on the nose. -/
theorem omegaCombinator_betaSelfStep :
    Step omegaCombinator omegaCombinator :=
  Step.beta

/-- Ω is NOT strongly normalizing: it steps to itself, so under the
one-step-successor relation it would have to be accessible from itself — which
`accessibleElementNotSelfRelated` rules out. -/
theorem omegaCombinator_notStronglyNormalizing :
    ¬ IsStronglyNormalizing omegaCombinator :=
  fun stronglyNormalizing =>
    accessibleElementNotSelfRelated stronglyNormalizing omegaCombinator_betaSelfStep

/-- The body `x x` of `λx. x x` has no outgoing `Step`: it is a neutral
application (the function head is a variable, not a λ, so the β rule cannot
fire — refuted by `Generator.noConfusion` on the head generators), and both
children are variables, which are normal leaves (`noStep_var`). -/
theorem selfApplicationBody_noStep
    (target : RawTerm 1)
    (bodyStep :
      Step (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) target) :
    False := by
  rcases Step.from_app bodyStep with
    ⟨_lambdaDomain, _lambdaBody, functionIsLambda, _⟩ |
    ⟨_functionAfter, _, functionStep⟩ |
    ⟨_argumentAfter, _, argumentStep⟩
  · exact Generator.noConfusion (congrArg RawTerm.rootGenerator functionIsLambda)
  · exact noStep_var (⟨0, Nat.succ_pos 0⟩ : Fin 1) functionStep
  · exact noStep_var (⟨0, Nat.succ_pos 0⟩ : Fin 1) argumentStep

/-- `λx. x x` IS strongly normalizing — it is a closed normal form with no
outgoing `Step` (any λ-step would have to step the body, but the body is
step-free by `selfApplicationBody_noStep`).  The contrast with `omegaCombinator`
is the whole point: SN is not preserved by self-application. -/
theorem selfApplicationLambda_stronglyNormalizing :
    IsStronglyNormalizing selfApplicationLambda :=
  isStronglyNormalizing_of_noStep
    (fun target lambdaStep => by
      rcases Step.from_lam lambdaStep with
        ⟨_domainAfter, _, domainStep⟩ | ⟨bodyAfter, _, bodyStep⟩
      · exact noStep_unit domainStep
      · exact selfApplicationBody_noStep bodyAfter bodyStep)

/-- ★ The SN-043 typing hypothesis is ESSENTIAL.  In the raw (untyped)
reduction system the application of a strongly-normalizing function to a
strongly-normalizing argument need NOT be strongly normalizing: take both to be
`λx. x x` (which is SN), whose application to itself is `Ω` (which is not SN).
So "well-typed ⟹ SN" (SN-043) genuinely relies on typing; raw reduction alone
is not normalizing, and the β-redex side condition the reducibility argument
discharges is load-bearing rather than cosmetic. -/
theorem applicationOfStronglyNormalizingNotAlwaysStronglyNormalizing :
    ∃ functionTerm argument : RawTerm 0,
      IsStronglyNormalizing functionTerm ∧
      IsStronglyNormalizing argument ∧
      ¬ IsStronglyNormalizing (appCell functionTerm argument) :=
  ⟨selfApplicationLambda, selfApplicationLambda,
    selfApplicationLambda_stronglyNormalizing,
    selfApplicationLambda_stronglyNormalizing,
    omegaCombinator_notStronglyNormalizing⟩

end FX1Poly.Typed
