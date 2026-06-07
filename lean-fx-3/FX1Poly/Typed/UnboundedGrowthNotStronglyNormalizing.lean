import FX1Poly.Typed.UntypedOmegaNotStronglyNormalizing

/-! # Foundation/PolyCell/Typed/UnboundedGrowthNotStronglyNormalizing
    — non-strong-normalization by UNBOUNDED GROWTH (a second, qualitatively different divergence shape)

`UntypedOmegaNotStronglyNormalizing.lean` exhibits the Ω combinator as a closed non-`IsStronglyNormalizing`
term, and the divergence there is the simplest possible shape: a one-step SELF-LOOP (`Step Ω Ω`).  Its
non-SN proof goes through `accessibleElementNotSelfRelated` — "an accessible element cannot be related to
itself" — which is exactly the 1-cycle special case.

This file exhibits the other archetypal divergence: a closed term that diverges by STRICTLY GROWING, never
returning to any earlier form.  The self-loop lemma cannot reach it (the term never steps to itself), so the
divergence is witnessed by the GENERAL principle behind strong normalization:

  * `accessibleElementHasNoInfiniteChain` — the general well-foundedness fact (sibling of
    `accessibleElementNotSelfRelated`): an `Acc`-element admits no infinite descending chain.  Proved
    propext-free by `Acc.rec` with the shifted-tail sequence fed back through the induction hypothesis.
  * `notStronglyNormalizing_of_infiniteReduction` — its reduction-theoretic face: ANY infinite `Step`
    sequence `t₀ → t₁ → t₂ → …` witnesses `¬ IsStronglyNormalizing t₀`.  This is the canonical
    characterization of non-SN, reusable for any future non-self-looping pathology.

The concrete witness is the "tripler" fixpoint:

  * `tripler = λx. (x x) x` and `growingDivergentTerm = (λx. (x x) x) (λx. (x x) x)`.  Its β-reduct is
    `(growingDivergentTerm) tripler` — one application LARGER than the source — so each reduct strictly
    grows: `growingReductionSequence n = (… ((growingDivergentTerm) tripler) … tripler)` with `n` trailing
    `tripler` applications.  `growingReductionSequence_steps` proves every term steps to the next (index 0
    by root β — the substitution `(x x) x [x := tripler]` computes definitionally to the larger term, the
    same nullary-substitution mechanism that makes Ω's self-step a bare `Step.beta`; index `n+1` by
    congruence into the function child, carrying the inductive step).
  * `growingDivergentTerm_notStronglyNormalizing` feeds that sequence to the general lemma.
  * `growingFirstReduct_ne_source` records (by the propext-free structural `DecidableEq`) that the first
    reduct genuinely DIFFERS from the source — the divergence is NOT a self-loop, so the general
    infinite-chain lemma, not `accessibleElementNotSelfRelated`, is what proves it.

`nonSelfLoopingDivergenceExists` packages the contrast with Ω: there is a closed non-SN term whose
witnessing reduction sequence is strictly growing (its first reduct differs from its source).  Together
with Ω (the self-loop) this exhibits both archetypes of untyped divergence — and both are excluded by
SN-043 (`HasTypeDescPi Γ t T → IsStronglyNormalizing t`), since neither is typable.

Everything is about the raw `Step` relation; no typing derivation is consulted.  Zero-axiom: the general
lemma is a direct `Acc.rec`; the sequence steps are `Step.beta` + the uniform congruence rule; the
inequality is `decide` over the propext-free `RawTermDecEq`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- **An accessible element admits no infinite descending chain.**  The general well-foundedness fact
behind strong normalization, and the sibling of `accessibleElementNotSelfRelated` (which is its 1-cycle
special case): if `headElement` is `Acc relation` and `chain` is an infinite sequence with each
`chain (index+1)` a `relation`-predecessor of `chain index` (and `chain 0 = headElement`), then `False`.
Proved propext-free by `Acc.rec`: at each point the first chain step exhibits `chain 1` as an accessor,
and the induction hypothesis is fed the shifted tail `fun index => chain (index + 1)`. -/
theorem accessibleElementHasNoInfiniteChain {carrier : Type}
    {relation : carrier → carrier → Prop} :
    ∀ (headElement : carrier), Acc relation headElement →
      ∀ (chain : Nat → carrier), chain 0 = headElement →
        (∀ index, relation (chain (index + 1)) (chain index)) → False :=
  fun _headElement accessible =>
    Acc.rec
      (motive := fun point _ =>
        ∀ chain : Nat → carrier, chain 0 = point →
          (∀ index, relation (chain (index + 1)) (chain index)) → False)
      (fun _point _accessors inductiveHypothesis chain chainHead chainSteps =>
        inductiveHypothesis (chain 1) (chainHead ▸ chainSteps 0)
          (fun index => chain (index + 1)) rfl (fun index => chainSteps (index + 1)))
      accessible

/-- **An infinite reduction sequence witnesses non-strong-normalization.**  If `reductionSequence` is an
infinite `Step` chain `t₀ → t₁ → t₂ → …`, then its head `t₀` is NOT `IsStronglyNormalizing`.  The
canonical characterization of non-SN — `IsStronglyNormalizing = Acc StepSuccessor`, and
`StepSuccessor (seq (i+1)) (seq i)` is exactly `Step (seq i) (seq (i+1))`, so the chain is an infinite
descending chain that `accessibleElementHasNoInfiniteChain` rules out.  Unlike
`accessibleElementNotSelfRelated`, the sequence need not be constant — this reaches strictly-growing
(never self-looping) divergence. -/
theorem notStronglyNormalizing_of_infiniteReduction {scope : Nat}
    (reductionSequence : Nat → RawTerm scope)
    (eachStepsToNext :
      ∀ index, Step (reductionSequence index) (reductionSequence (index + 1))) :
    ¬ IsStronglyNormalizing (reductionSequence 0) :=
  fun stronglyNormalizing =>
    accessibleElementHasNoInfiniteChain (reductionSequence 0) stronglyNormalizing
      reductionSequence rfl eachStepsToNext

/-- `λx. (x x) x` — the bound variable applied to itself, then to itself once more.  Closed at scope `0`.
Unlike `λx. x x` (whose self-application is Ω and loops in place), this triples the occurrence, so its
self-application grows by one application per β-step. -/
def tripler : RawTerm 0 :=
  lamCell (appCell (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
    (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
    (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))

/-- `(λx. (x x) x) (λx. (x x) x)` — a closed term that diverges by UNBOUNDED GROWTH: its β-reduct is
`(growingDivergentTerm) tripler`, strictly larger than itself. -/
def growingDivergentTerm : RawTerm 0 := appCell tripler tripler

/-- The strictly-growing reduction sequence out of `growingDivergentTerm`: each term is the previous one
applied to one more copy of `tripler`.  `growingReductionSequence 0` is the source; the `(n+1)`-th wraps
the `n`-th in `appCell _ tripler`. -/
def growingReductionSequence : Nat → RawTerm 0
  | 0 => growingDivergentTerm
  | n + 1 => appCell (growingReductionSequence n) tripler

/-- Every term in the growing sequence steps to the next.  Index `0`: the root β-redex
`(λx. (x x) x) tripler` contracts to `(tripler tripler) tripler = (growingDivergentTerm) tripler` (the
substitution computes definitionally, exactly as Ω's self-step is a bare `Step.beta`).  Index `n+1`: a
congruence step into the FUNCTION child (`StepChildren.here`), carrying the inductive step
`growingReductionSequence_steps n`. -/
theorem growingReductionSequence_steps :
    ∀ index, Step (growingReductionSequence index) (growingReductionSequence (index + 1))
  | 0 => Step.beta
  | n + 1 =>
    Step.cong .gen_app ()
      (StepChildren.here
        (parentScope := 0) (headShift := 0) (restShifts := [0])
        ((.childCons tripler .childNil) : RawTermChildren [0] 0)
        (growingReductionSequence_steps n))

/-- ★ `growingDivergentTerm` is NOT strongly normalizing — witnessed by its strictly-growing infinite
reduction sequence through the general `notStronglyNormalizing_of_infiniteReduction` lemma.  A divergence
qualitatively different from Ω: the term never returns to an earlier form, so the self-loop lemma
`accessibleElementNotSelfRelated` cannot prove it; the general infinite-chain principle is required. -/
theorem growingDivergentTerm_notStronglyNormalizing :
    ¬ IsStronglyNormalizing growingDivergentTerm :=
  notStronglyNormalizing_of_infiniteReduction growingReductionSequence growingReductionSequence_steps

/-- The first reduct genuinely DIFFERS from the source: `growingReductionSequence 1 ≠
growingReductionSequence 0`.  Decided by the propext-free structural `DecidableEq (RawTerm 0)`.  This is
the concrete contrast with Ω (whose β-reduct equals itself); the witnessing sequence here is strictly
growing, so this divergence is genuinely not a self-loop. -/
theorem growingFirstReduct_ne_source :
    growingReductionSequence 1 ≠ growingReductionSequence 0 := by
  decide

/-- ★ There is a closed non-strongly-normalizing term whose witnessing reduction sequence is strictly
GROWING (its first reduct differs from its source) — the unbounded-growth archetype of divergence,
distinct from Ω's self-loop.  Together with `omegaCombinator` this exhibits both shapes of untyped
divergence; both are excluded by SN-043 because neither is typable. -/
theorem nonSelfLoopingDivergenceExists :
    ∃ reductionSequence : Nat → RawTerm 0,
      reductionSequence 0 = growingDivergentTerm ∧
      (∀ index, Step (reductionSequence index) (reductionSequence (index + 1))) ∧
      reductionSequence 1 ≠ reductionSequence 0 ∧
      ¬ IsStronglyNormalizing (reductionSequence 0) :=
  ⟨growingReductionSequence, rfl, growingReductionSequence_steps,
    growingFirstReduct_ne_source, growingDivergentTerm_notStronglyNormalizing⟩

end FX1Poly.Typed
