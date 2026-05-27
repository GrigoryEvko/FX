import LeanFX2.Foundation.PolyCell.Core.RawTermV2Subst

/-! # Foundation/PolyCell/Core/RawTermV2SubstPointwise — Allais extensionality

This file ships the **Allais extensionality theorem** for foldV2:
**pointwise-equal substitutions act equally on terms**.

This is the FIRST of three Action laws V2-L2.7 needs:

1. **apply_ext** (THIS FILE)   — `(∀ pos, sigma1 pos = sigma2 pos) →
                                  term.subst sigma1 = term.subst sigma2`
2. **identity_apply** (next)    — `term.subst identity = term`
3. **compose_assoc** (next)     — `(term.subst s1).subst s2 = term.subst (s1.compose s2)`

Together they witness the polynomial-monad laws at the term layer.
Once all three ship, the `Action RawTermSubstV2` instance closes
zero-axiom.

## The L2 cascade-tax killer at work

v1's `RawTerm.subst_pointwise` (Foundation/RawSubst/SubstLemmas.lean,
lines 40-220) is a **74-arm structural induction** — one arm per
RawTerm constructor.  Each arm is one line of `dsimp + rw`, but
adding a new term former requires adding a new arm.  That cascade is
load-bearing for the polynomial-monad fusion ladder; in v1 it costs
roughly 5-8 K LoC across the rename / subst / weaken / substHet trio.

v2's version collapses to a **single mutual induction** with FOUR
structural arms:

  * `.mkGen` term arm:
    - `.gen_var` sub-case (dispatches via `varToRawTermV2`)
    - non-`.gen_var` sub-case (dispatches via algebra)
  * `RawTermChildrenV2` arms:
    - `.childNil`
    - `.childCons`

The 194-generator dispatch is amortized into foldV2 (#177) ONCE
across the kernel.  Adding a new Generator requires NO new
pointwise arm — the proof closes for the new generator automatically
through the non-var sub-case.

This is the empirical L2 demonstration #181 needs to make:
**the cascade tax is dead**.

## Mutual structural induction

`RawTermV2.subst_pointwise` and `RawTermChildrenV2.subst_pointwise`
mutually invoke each other through foldV2's term-children recursion.
Lean's structural mutual recursion handles termination — the same
mechanism that makes foldV2 well-defined (sub-parts of one mutual
block).

In the non-variable case, `subst_pointwise` threads the pointwise-eq
through `iterateLiftRaw` (the per-binder Container lifter) via
`iterateLiftRaw_RawTermSubstV2_pointwise`, then recurses on children.

In the `.childCons` case, the head child sits under
`headShift`-many additional binders, so the pointwise-eq must lift
through `iterateLiftRaw` before recursing on the head.  The tail
recurses with the original pointwise-eq.

## Why a `PointwiseEq` Prop, not function equality

Function-typed substitutions cannot admit `sigma1 = sigma2` (data
equality) without funext.  Funext is BANNED (it transitively pulls
propext via the function-extensionality lemma's standard
formulation).

The standard Allais workaround: state laws **pointwise** as the
proposition `∀ pos, sigma1 pos = sigma2 pos`.  This makes the
laws funext-free and zero-axiom — exactly the discipline v1's
`RawTermSubst.lift_pointwise` (Foundation/RawSubst/SubstLemmas.lean
line 30) already uses.

## Zero-axiom verification

All declarations propext-free:
* `PointwiseEq` — Prop definition (no equation lemmas)
* `PointwiseEq.refl` — `fun _ => Eq.refl _`
* `RawTermSubstV2.lift_pointwise` — Fin pattern match on 0 / k+1
  (per `feedback_lean_fin_cases_axiom` — direct `⟨0, _⟩` / `⟨k+1, _⟩`
  structure matching is axiom-clean)
* `iterateLiftRaw_RawTermSubstV2_pointwise` — Nat induction (`zero` /
  `succ`)
* `RawTermV2.subst_pointwise` / `RawTermChildrenV2.subst_pointwise` —
  mutual structural match on `RawTermV2` / `RawTermChildrenV2`
  (full-enum, no wildcards), with binary `by_cases hVar` on
  `Generator`'s `DecidableEq` (which is propext-free per V2-L0.11
  `instDecidableEqGenerator`)

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-! ## Section 1 — The pointwise-equality predicate

We avoid funext by carrying pointwise equality as a Prop-valued
relation throughout the Action-law machinery.  Concrete instances
(`RawTermSubstV2.identity`, `RawTermSubstV2.compose`, etc.) prove
pointwise relationships via this predicate rather than via function
equality.
-/

/-- Pointwise equality of substitutions.

Two substitutions agree pointwise when they produce the same
substituent for every variable position.  This is the propositional
analog of function equality, sidestepping funext.

Used by `lift_pointwise`, `iterateLiftRaw_pointwise`, and
`RawTermV2.subst_pointwise` to thread agreement through binder
crossings and recursive structure. -/
def RawTermSubstV2.PointwiseEq {sourceScope targetScope : Nat}
    (firstSubstitution secondSubstitution :
        RawTermSubstV2 sourceScope targetScope) : Prop :=
  ∀ position : Fin sourceScope,
    firstSubstitution position = secondSubstitution position

/-- Pointwise equality is reflexive: every substitution agrees with
itself at every position. -/
theorem RawTermSubstV2.PointwiseEq.refl {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope targetScope) :
    RawTermSubstV2.PointwiseEq someSubstitution someSubstitution :=
  fun _ => Eq.refl _

/-! ## Section 2 — Binder lifts respect pointwise equality

These two lemmas thread `PointwiseEq` through the binder crossings
foldV2 performs.  `lift_pointwise` handles a single binder;
`iterateLiftRaw_RawTermSubstV2_pointwise` handles arbitrary depths
(needed for generators like `lam` that bind one variable, plus any
future generators that bind multiple). -/

/-- Lifting respects pointwise equality.

Given two substitutions that agree on every source position, their
single-binder lifts agree on every position in the extended scope.

* Variable 0 in the lifted scope: both lifts produce the same fresh
  `gen_var 0` term (definitional, closes by `rfl`).
* Variable k+1 in the lifted scope: both lifts produce
  `RawTermV2.weaken (sigma_i ⟨k, _⟩)`; congruence of `weaken` over
  the pointwise hypothesis closes the goal via `rw`. -/
theorem RawTermSubstV2.lift_pointwise {sourceScope targetScope : Nat}
    {firstSubstitution secondSubstitution :
        RawTermSubstV2 sourceScope targetScope}
    (substEq :
        RawTermSubstV2.PointwiseEq firstSubstitution secondSubstitution) :
    RawTermSubstV2.PointwiseEq
        firstSubstitution.lift
        secondSubstitution.lift := by
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨priorPositionValue + 1, hBound⟩ =>
      show RawTermV2.weaken
              (firstSubstitution
                  ⟨priorPositionValue, Nat.lt_of_succ_lt_succ hBound⟩) =
            RawTermV2.weaken
              (secondSubstitution
                  ⟨priorPositionValue, Nat.lt_of_succ_lt_succ hBound⟩)
      rw [substEq ⟨priorPositionValue, Nat.lt_of_succ_lt_succ hBound⟩]

/-- Iterated lift respects pointwise equality.

At any binder depth, `iterateLiftRaw` preserves the pointwise
agreement of two substitutions.

Proof: induction on `binderDepth`.
* `zero`: `iterateLiftRaw sigma 0 = sigma` (by `iterateLiftRaw`'s
  defn), so the pointwise-eq passes through unchanged.
* `succ priorDepth`: `iterateLiftRaw sigma (priorDepth + 1) =
  LiftsRaw.liftForRaw (iterateLiftRaw sigma priorDepth)`.  The IH
  gives pointwise-eq at depth `priorDepth`; `lift_pointwise` lifts
  through one binder. -/
theorem iterateLiftRaw_RawTermSubstV2_pointwise {sourceScope targetScope : Nat}
    {firstSubstitution secondSubstitution :
        RawTermSubstV2 sourceScope targetScope}
    (substEq :
        RawTermSubstV2.PointwiseEq firstSubstitution secondSubstitution)
    (binderDepth : Nat) :
    RawTermSubstV2.PointwiseEq
        (iterateLiftRaw firstSubstitution binderDepth)
        (iterateLiftRaw secondSubstitution binderDepth) := by
  induction binderDepth with
  | zero => exact substEq
  | succ _priorDepth priorIH =>
      exact RawTermSubstV2.lift_pointwise priorIH

/-! ## Section 3 — The Allais extensionality theorem (mutual induction)

This is the L2 cascade-tax killer demonstration.  In v1, the analog
`RawTerm.subst_pointwise` is 74 per-ctor arms (one per term former).
In v2, the proof collapses to a single mutual structural induction
with four arms total — and adding a new Generator requires NO new
arm.

The proof uses `by_cases` on Generator's `DecidableEq` (propext-free
per V2-L0.11) to dispatch between the variable and non-variable arms
of foldV2.  Both branches are taken simultaneously on both sides of
the equation because the dispatch depends only on the term (not the
substitution), so the two sides always agree on which arm to take. -/

mutual

/-- Allais extensionality: pointwise-equal substitutions produce
equal subst results on any term.

This is the v2 replacement for v1's 74-arm `RawTerm.subst_pointwise`.
Adding a new Generator does NOT require adding a new arm here — the
proof closes uniformly through the non-variable case via the children
spine recursion. -/
theorem RawTermV2.subst_pointwise {sourceScope targetScope : Nat}
    {firstSubstitution secondSubstitution :
        RawTermSubstV2 sourceScope targetScope}
    (substEq :
        RawTermSubstV2.PointwiseEq firstSubstitution secondSubstitution)
    (sourceTerm : RawTermV2 sourceScope) :
    RawTermV2.subst firstSubstitution sourceTerm =
      RawTermV2.subst secondSubstitution sourceTerm := by
  match sourceTerm with
  | .mkGen someGenerator somePayload someChildren =>
    by_cases hVar : someGenerator = .gen_var
    case pos =>
      -- Variable arm: subst reduces to `varToRawTermV2 sigma_i payload`
      -- which is `sigma_i payload` for RawTermSubstV2's
      -- ActsOnRawTermV2Var instance.  The pointwise hypothesis closes
      -- the goal directly.
      subst hVar
      -- After subst, somePayload : Generator.payload .gen_var sourceScope
      -- which is Fin sourceScope by Generator.payload's defn at .gen_var.
      -- foldV2 dispatches the `if hVar : .gen_var = .gen_var` to the
      -- pos branch via Generator.decEq's canonical isTrue, and the
      -- Eq.rec cast reduces to identity since the equality is rfl.
      show ActsOnRawTermV2Var.varToRawTermV2 firstSubstitution somePayload =
            ActsOnRawTermV2Var.varToRawTermV2 secondSubstitution somePayload
      -- For RawTermSubstV2's ActsOnRawTermV2Var instance:
      -- varToRawTermV2 sigma pos = sigma pos
      exact substEq somePayload
    case neg =>
      -- Non-variable arm: subst reduces to `algebra g (cast payload)
      -- (foldChildrenV2 sigma_i children)`.  The algebra and the cast
      -- payload are sigma-independent; only the folded children differ.
      -- The children IH (mutual) closes the goal.
      --
      -- CRITICAL: use `dsimp only [foldV2]` rather than `unfold foldV2`.
      -- `unfold` on a mutual recursive def pulls `Quot.sound` via the
      -- equation lemma generation pipeline (confirmed empirically
      -- 2026-05-27, see feedback_lean_unfold_mutual_quot_sound).
      -- `dsimp only` uses definitional reduction without the equation
      -- lemma engine, keeping the proof zero-axiom.
      show RawTermV2.subst firstSubstitution
              (.mkGen someGenerator somePayload someChildren) =
            RawTermV2.subst secondSubstitution
              (.mkGen someGenerator somePayload someChildren)
      dsimp only [RawTermV2.subst, foldV2]
      simp only [dif_neg hVar]
      congr 1
      exact RawTermChildrenV2.subst_pointwise substEq someChildren

/-- Allais extensionality on children spines: pointwise-equal
substitutions produce equal foldChildrenV2 results.

In v1 this lemma is fused into the term-level pointwise (no separate
children-spine).  In v2, the mutual structure of RawTermV2 /
RawTermChildrenV2 means children get their own pointwise theorem,
which is invoked by the non-variable arm of subst_pointwise. -/
theorem RawTermChildrenV2.subst_pointwise
    {sourceScope targetScope : Nat}
    {firstSubstitution secondSubstitution :
        RawTermSubstV2 sourceScope targetScope}
    (substEq :
        RawTermSubstV2.PointwiseEq firstSubstitution secondSubstitution)
    {binderShifts : List Nat}
    (someChildren : RawTermChildrenV2 binderShifts sourceScope) :
    RawTermChildrenV2.subst firstSubstitution someChildren =
      RawTermChildrenV2.subst secondSubstitution someChildren := by
  match binderShifts, someChildren with
  | [], .childNil =>
      -- Empty spine: both sides reduce to .childNil by foldChildrenV2's
      -- nil arm.
      rfl
  | headShift :: _, .childCons childHead childTail =>
      -- Cons spine: head is lifted by headShift, tail unchanged.
      -- Both head and tail subst differ between sigma1 and sigma2, so
      -- we apply the IHs on both, threading the pointwise-eq through
      -- iterateLiftRaw for the head.
      show RawTermChildrenV2.childCons
              (RawTermV2.subst
                  (iterateLiftRaw firstSubstitution headShift) childHead)
              (RawTermChildrenV2.subst firstSubstitution childTail) =
            RawTermChildrenV2.childCons
              (RawTermV2.subst
                  (iterateLiftRaw secondSubstitution headShift) childHead)
              (RawTermChildrenV2.subst secondSubstitution childTail)
      have headEqualityWitness :=
        RawTermV2.subst_pointwise
          (iterateLiftRaw_RawTermSubstV2_pointwise substEq headShift)
          childHead
      have tailEqualityWitness :=
        RawTermChildrenV2.subst_pointwise substEq childTail
      rw [headEqualityWitness, tailEqualityWitness]

end -- mutual

/-! ## Section 4 — Smoke tests

Verify the headline `RawTermV2.subst_pointwise` invokes cleanly on
representative terms.

These are sanity checks — the real consumers are V2-L2.7b
(`subst_identity_apply` uses `subst_pointwise` to bridge between the
literal `identity` and `iterateLiftRaw identity n`) and V2-L2.7c
(`subst_compose` similarly). -/

/-- Smoke test: subst_pointwise on `.gen_unit` is `rfl` (the term has
no variables, so no pointwise-eq usage).

Demonstrates that `subst_pointwise` is well-typed and reduces on
closed inputs. -/
theorem RawTermV2.subst_pointwise_unit_smoke {scope : Nat}
    {firstSubstitution secondSubstitution :
        RawTermSubstV2 scope scope}
    (substEq :
        RawTermSubstV2.PointwiseEq firstSubstitution secondSubstitution) :
    RawTermV2.subst firstSubstitution
        (.mkGen .gen_unit () .childNil : RawTermV2 scope) =
      RawTermV2.subst secondSubstitution
        (.mkGen .gen_unit () .childNil : RawTermV2 scope) :=
  RawTermV2.subst_pointwise substEq _

/-- Smoke test: subst_pointwise on `.gen_var` uses the pointwise
hypothesis at the variable's position.

Exercises the variable arm of the mutual induction. -/
theorem RawTermV2.subst_pointwise_var_smoke {scope : Nat}
    {firstSubstitution secondSubstitution :
        RawTermSubstV2 (scope + 1) (scope + 1)}
    (substEq :
        RawTermSubstV2.PointwiseEq firstSubstitution secondSubstitution) :
    RawTermV2.subst firstSubstitution
        (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
                .childNil) =
      RawTermV2.subst secondSubstitution
        (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
                .childNil) :=
  RawTermV2.subst_pointwise substEq _

end LeanFX2.Foundation.PolyCell.Core
