import FX1Poly.Core.StepRewriteRuleMap
import FX1Poly.Core.StepStar

/-! # FX1Poly/Core/StepWordRewriteSoundness
    — the FX reduction relation embeds into word rewriting over the term-code monoid

`StepRewriteRuleMap` maps each FX `Step` to a rewrite rule `⟨redex.toCode, reduct.toCode⟩` and assembles the
generated rule system `fxStepSystem`.  This file builds the one-step / many-step WORD-REWRITING relation that system drives
(over the term-code word monoid `List Nat`), and proves the FORWARD half of the Leg-3 bridge: every FX reduction
is a word rewrite under `fxStepSystem` — `Step a b ⟹ FxWordRewritesOneStep fxStepSystem a.toCode b.toCode`, and
its many-step closure `StepStar a b ⟹ FxWordRewritesMany …`.

The existing one-step rewriting (`Rewrite.lean`'s `OmegacEWord.RewritesOneStep`) is over the abstract scaffold
word `OmegacEWord` — the wrong alphabet for the 194-generator kernel.  Here the words are the FX term codes
(`List Nat` via the shipped `RawTerm.toCode`), and the relation is closed under left/right word context by
construction (the congruence with concatenation).

## Why soundness is the `fire` lift (and is NOT gated on typed SN)

`fxStepSystem` contains every reduction's FULLY-INSTANTIATED code pair as a top-level rule — including each `cong`
(in-context) step, whose endpoints are already the in-context redex/reduct codes.  So one-step soundness is a
single `FxWordRewritesOneStep.fire` of the system rule `StepRewriteRuleMap` proves is a member.  No context-closure
unfolding, no substitution analysis, no termination is needed for THIS direction.  The depth — and the typed-SN gate
per `core_raw_sn_false_natrec` — lives in the REVERSE half (completeness / inversion: a word rewrite comes
from an actual `Step`, which needs decode) and in termination / confluence.

## What is proved

* `FxWordRewritesOneStep` — one-step word rewriting under an `FxTermRewriteRule` system, closed under left/right
  word context (`fire` / `underLeftContext` / `underRightContext`).
* `Step.toWordRewrite` — **single-step soundness**: `Step a b ⟹ FxWordRewritesOneStep fxStepSystem a.toCode
  b.toCode` (the `fire` of the system rule).
* `FxWordRewritesMany` — the reflexive-transitive closure (`refl` / `step`), with `single`, `trans`, and the
  many-step context lifts `underLeftContext` / `underRightContext` — a genuine congruence preorder.
* `StepStar.toWordRewrites` — **many-step soundness**: `StepStar a b ⟹ FxWordRewritesMany fxStepSystem a.toCode
  b.toCode` (induction over the reduction chain).

## Zero-axiom verification

The relations are plain `Prop` inductives; `Step.toWordRewrite` is a constructor application (`fire`); the many-step
soundness, `trans`, and the context lifts are structural inductions over the chains.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **One-step word rewriting** over the term-code word monoid (`List Nat`) under an `FxTermRewriteRule` system.
A system rule `fire`s at the top level; the relation is closed under left/right word context (the congruence
with concatenation), so a rule fires inside any surrounding code word. -/
inductive FxWordRewritesOneStep (system : FxTermRewriteRule → Prop) :
    List Nat → List Nat → Prop where
  /-- Fire a system rule at the top level. -/
  | fire (rule : FxTermRewriteRule) (isInSystem : system rule) :
      FxWordRewritesOneStep system rule.leftHandSide rule.rightHandSide
  /-- Rewrite inside a left word context. -/
  | underLeftContext (prefixWord : List Nat) {sourceWord targetWord : List Nat}
      (inner : FxWordRewritesOneStep system sourceWord targetWord) :
      FxWordRewritesOneStep system (prefixWord ++ sourceWord) (prefixWord ++ targetWord)
  /-- Rewrite inside a right word context. -/
  | underRightContext (suffixWord : List Nat) {sourceWord targetWord : List Nat}
      (inner : FxWordRewritesOneStep system sourceWord targetWord) :
      FxWordRewritesOneStep system (sourceWord ++ suffixWord) (targetWord ++ suffixWord)

/-- **Single-step bridge soundness**: every FX reduction is a one-step word rewrite under the generated system.
The induced rule `⟨a.toCode, b.toCode⟩` is a member of `fxStepSystem`, so it `fire`s. -/
theorem Step.toWordRewrite {scope : Nat} {redex reduct : RawTerm scope}
    (step : Step redex reduct) :
    FxWordRewritesOneStep fxStepSystem redex.toCode reduct.toCode :=
  FxWordRewritesOneStep.fire step.inducedRewriteRule step.inducedRewriteRule_mem_fxStepSystem

/-- **Many-step word rewriting**: the reflexive-transitive closure of one-step rewriting — full code-word
reduction modulo the rule system. -/
inductive FxWordRewritesMany (system : FxTermRewriteRule → Prop) :
    List Nat → List Nat → Prop where
  /-- Reflexivity (length-zero rewrite). -/
  | refl (word : List Nat) : FxWordRewritesMany system word word
  /-- One step, then a shorter chain. -/
  | step {sourceWord middleWord targetWord : List Nat}
      (head : FxWordRewritesOneStep system sourceWord middleWord)
      (tail : FxWordRewritesMany system middleWord targetWord) :
      FxWordRewritesMany system sourceWord targetWord

/-- A single rewrite step is a many-step rewrite. -/
theorem FxWordRewritesMany.single {system : FxTermRewriteRule → Prop}
    {sourceWord targetWord : List Nat}
    (oneStep : FxWordRewritesOneStep system sourceWord targetWord) :
    FxWordRewritesMany system sourceWord targetWord :=
  FxWordRewritesMany.step oneStep (FxWordRewritesMany.refl targetWord)

/-- Many-step rewriting is transitive (compose two reduction sequences). -/
theorem FxWordRewritesMany.trans {system : FxTermRewriteRule → Prop}
    {firstWord middleWord lastWord : List Nat}
    (firstChain : FxWordRewritesMany system firstWord middleWord)
    (secondChain : FxWordRewritesMany system middleWord lastWord) :
    FxWordRewritesMany system firstWord lastWord := by
  induction firstChain with
  | refl _ => exact secondChain
  | step head _tail tailIH => exact FxWordRewritesMany.step head (tailIH secondChain)

/-- Many-step rewriting is closed under a left word context. -/
theorem FxWordRewritesMany.underLeftContext {system : FxTermRewriteRule → Prop}
    (prefixWord : List Nat) {sourceWord targetWord : List Nat}
    (chain : FxWordRewritesMany system sourceWord targetWord) :
    FxWordRewritesMany system (prefixWord ++ sourceWord) (prefixWord ++ targetWord) := by
  induction chain with
  | refl word => exact FxWordRewritesMany.refl (prefixWord ++ word)
  | step head _tail tailIH =>
      exact FxWordRewritesMany.step (FxWordRewritesOneStep.underLeftContext prefixWord head) tailIH

/-- Many-step rewriting is closed under a right word context. -/
theorem FxWordRewritesMany.underRightContext {system : FxTermRewriteRule → Prop}
    (suffixWord : List Nat) {sourceWord targetWord : List Nat}
    (chain : FxWordRewritesMany system sourceWord targetWord) :
    FxWordRewritesMany system (sourceWord ++ suffixWord) (targetWord ++ suffixWord) := by
  induction chain with
  | refl word => exact FxWordRewritesMany.refl (word ++ suffixWord)
  | step head _tail tailIH =>
      exact FxWordRewritesMany.step (FxWordRewritesOneStep.underRightContext suffixWord head) tailIH

/-- **Many-step bridge soundness**: every FX reduction SEQUENCE is a word-rewrite sequence under the generated
system.  By induction on the `StepStar` chain: reflexivity maps to reflexivity, and a `Step`-then-tail chain
maps to a one-step word rewrite (`Step.toWordRewrite`) followed by the tail's word rewrites. -/
theorem StepStar.toWordRewrites {scope : Nat} {startTerm finalTerm : RawTerm scope}
    (steps : StepStar startTerm finalTerm) :
    FxWordRewritesMany fxStepSystem startTerm.toCode finalTerm.toCode := by
  induction steps with
  | refl term => exact FxWordRewritesMany.refl term.toCode
  | trans headStep _tailStar tailIH =>
      exact FxWordRewritesMany.step headStep.toWordRewrite tailIH

end FX1Poly.Core
