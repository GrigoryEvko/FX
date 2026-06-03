import FX1Poly.Core.StepStarConfluence
import FX1Poly.Core.DiamondConfluence

/-! # FX1Poly/Core/StepParallelConfluence
    — wiring the abstract diamond/strip confluence to the FX raw `StepStar` (M8-S1, #420)

`StepStarConfluence.lean` factors raw global confluence HONESTLY: the shipped `cd_lemma` is only a LOCAL
(single-step/single-step) join, and `StepStar.HasConfluence` is supplied conditionally — via
`confluence_of_strongNormalization` (needs raw SN, which is FALSE for raw beta+iota: `gen_natRec`/`gen_fixedPoint`
diverge) or via `confluence_of_strip` (needs the strip property `HasStrip`).  The file's own docstring says the
strip property is meant to be "supplied from a parallel-reduction diamond."

`DiamondConfluence.lean` (the previous task) proves exactly that abstract content — confluence from a DIAMOND with
no termination, the Tait/Martin-Löf/Takahashi method — but as a free-standing metatheorem over an arbitrary
relation.  This file is the ADAPTER that connects the two: given any parallel relation `ParStep` sandwiched
`Step ⊆ ParStep ⊆ StepStar` whose `DiamondProperty` holds, it discharges BOTH the FX strip property and FX global
confluence.  The single remaining mathematical obligation — exhibit a concrete FX parallel reduction and prove its
diamond (the Takahashi complete-development argument over the 194-generator tree) — is the cleanly-stated
hypothesis, deferred to a downstream task; it is NOT faked here.

This is the genuine FX-layer realization of `#420` (`parStar.confluence`): the generic diamond core is shipped, and
this file is the bridge from that core to the concrete `StepStar.HasConfluence` target.  Raw beta+iota confluence is
UNBLOCKED by this route precisely because it needs confluence, not termination (raw `Step` is not SN).

## What is proved

* `StepStar.toReflTransClosure` / `ofReflTransClosure` — the `StepStar` (left-extension) closure is isomorphic to
  the abstract `ReflTransClosure Step` (head-extension) from `Newman.lean`; both directions by structural induction.
* `StepStar.hasConfluence_of_parallelDiamond` — **route A (direct diamond)**: a sandwiched parallel relation with
  the diamond yields `StepStar.HasConfluence`, via the abstract `confluentOfDiamondSimulation` and the two bridges.
* `StepStar.hasStrip_of_parallelDiamond` — **route B (strip)**: the same hypotheses discharge the FX strip property
  `StepStar.HasStrip` via the abstract `stripLemma`, realizing the promise in `StepStarConfluence.lean`'s docstring
  (feed it to the shipped `confluence_of_strip` to recover confluence through the file's intended spine).

## Zero-axiom verification

All proofs are structural inductions over `StepStar` / `ReflTransClosure` plus `obtain` on the diamond/strip
existentials.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- The `StepStar` left-extension closure embeds into the abstract head-extension `ReflTransClosure Step`. -/
theorem StepStar.toReflTransClosure {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) : ReflTransClosure (@Step scope) source target := by
  induction chain with
  | refl term => exact ReflTransClosure.refl term
  | trans headStep _rest inductionHypothesis =>
      exact ReflTransClosure.head headStep inductionHypothesis

/-- The abstract `ReflTransClosure Step` collapses back into `StepStar` (the two closures are isomorphic). -/
theorem StepStar.ofReflTransClosure {scope : Nat} {source target : RawTerm scope}
    (chain : ReflTransClosure (@Step scope) source target) : StepStar source target := by
  induction chain with
  | refl term => exact StepStar.refl term
  | head firstStep _rest inductionHypothesis =>
      exact StepStar.trans firstStep inductionHypothesis

/-- **Route A (direct diamond).**  A parallel relation `ParStep` with `Step ⊆ ParStep ⊆ StepStar` whose
`DiamondProperty` holds at every scope makes the FX raw `StepStar` globally confluent.  Per scope, instantiate the
abstract `confluentOfDiamondSimulation` at `Carrier := RawTerm scope`, lift both diverging `StepStar` chains to the
abstract `ReflTransClosure Step`, and collapse the resulting join back to a `StepStar.Join`.

The diamond hypothesis `parDiamond` is the real mathematical content (the Takahashi complete-development argument);
it is honestly deferred to the construction of a concrete FX parallel reduction. -/
theorem StepStar.hasConfluence_of_parallelDiamond
    (ParStep : {scope : Nat} → RawTerm scope → RawTerm scope → Prop)
    (stepToPar : ∀ {scope : Nat} {a b : RawTerm scope}, Step a b → ParStep a b)
    (parToStepStar : ∀ {scope : Nat} {a b : RawTerm scope}, ParStep a b → StepStar a b)
    (parDiamond : ∀ {scope : Nat}, DiamondProperty (@ParStep scope)) :
    StepStar.HasConfluence := by
  intro scope source leftReduct rightReduct leftChain rightChain
  obtain ⟨commonReduct, leftJoin, rightJoin⟩ :=
    confluentOfDiamondSimulation (rel := @Step scope) (parRel := @ParStep scope)
      (fun {_ _} stepWitness => stepToPar stepWitness)
      (fun {_ _} parWitness => (parToStepStar parWitness).toReflTransClosure)
      parDiamond leftChain.toReflTransClosure rightChain.toReflTransClosure
  exact ⟨commonReduct, StepStar.ofReflTransClosure leftJoin, StepStar.ofReflTransClosure rightJoin⟩

/-- **Route B (strip).**  The same parallel-diamond hypotheses discharge the FX strip property `StepStar.HasStrip`:
lift the diverging `StepStar` chain to an abstract `ReflTransClosure ParStep`, strip the single (parallel-lifted)
step against it with the abstract `stripLemma`, and collapse the two parallel joins back to `StepStar`.  Feeding the
result to the shipped `StepStar.confluence_of_strip` recovers confluence through `StepStarConfluence.lean`'s intended
strip-to-Church-Rosser spine, realizing that file's "supplied from a parallel-reduction diamond" promise. -/
theorem StepStar.hasStrip_of_parallelDiamond
    (ParStep : {scope : Nat} → RawTerm scope → RawTerm scope → Prop)
    (stepToPar : ∀ {scope : Nat} {a b : RawTerm scope}, Step a b → ParStep a b)
    (parToStepStar : ∀ {scope : Nat} {a b : RawTerm scope}, ParStep a b → StepStar a b)
    (parDiamond : ∀ {scope : Nat}, DiamondProperty (@ParStep scope)) :
    StepStar.HasStrip := by
  intro scope source leftReduct rightReduct oneStep manyChain
  have liftManyToPar : ∀ {a b : RawTerm scope},
      StepStar a b → ReflTransClosure (@ParStep scope) a b := by
    intro a b chain
    induction chain with
    | refl term => exact ReflTransClosure.refl term
    | trans headStep _rest inductionHypothesis =>
        exact ReflTransClosure.head (stepToPar headStep) inductionHypothesis
  have collapseParToStepStar : ∀ {a b : RawTerm scope},
      ReflTransClosure (@ParStep scope) a b → StepStar a b := by
    intro a b chain
    induction chain with
    | refl term => exact StepStar.refl term
    | head firstStep _rest inductionHypothesis =>
        exact (parToStepStar firstStep).trans_compose inductionHypothesis
  obtain ⟨joinPoint, oneToJoin, manyToJoin⟩ :=
    stripLemma parDiamond (liftManyToPar manyChain) (stepToPar oneStep)
  exact ⟨joinPoint, collapseParToStepStar oneToJoin, collapseParToStepStar manyToJoin⟩

end FX1Poly.Core
