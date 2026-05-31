import FX1Poly.Core.RawTermSubst

/-! # Foundation/PolyCell/Core/RawTermSubstPointwise — Allais extensionality

The **Allais extensionality theorem** for fold:
**pointwise-equal substitutions act equally on terms**.

The **first of three Action laws**:

1. **apply_ext** (THIS FILE)   — `(∀ pos, sigma1 pos = sigma2 pos) →
                                  term.subst sigma1 = term.subst sigma2`
2. **identity_apply**           — `term.subst identity = term`
3. **compose_assoc**            — `(term.subst s1).subst s2 = term.subst (s1.compose s2)`

Together they witness the polynomial-monad laws at the term layer,
closing the `Action RawTermSubst` instance zero-axiom.

## A single mutual induction

The proof is a **single mutual induction** with FOUR structural arms:

  * `.mkGen` term arm:
    - `.gen_var` sub-case (dispatches via `varToRawTerm`)
    - non-`.gen_var` sub-case (dispatches via algebra)
  * `RawTermChildren` arms:
    - `.childNil`
    - `.childCons`

The 194-generator dispatch is amortized into fold ONCE across the
kernel.  Adding a new Generator requires NO new pointwise arm — the
proof closes for the new generator automatically through the non-var
sub-case.

## Mutual structural induction

`RawTerm.subst_pointwise` and `RawTermChildren.subst_pointwise`
mutually invoke each other through fold's term-children recursion.
Lean's structural mutual recursion handles termination — the same
mechanism that makes fold well-defined (sub-parts of one mutual
block).

In the non-variable case, `subst_pointwise` threads the pointwise-eq
through `iterateLiftRaw` (the per-binder Container lifter) via
`iterateLiftRaw_RawTermSubst_pointwise`, then recurses on children.

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
laws funext-free and zero-axiom.

## Zero-axiom verification

All declarations propext-free:
* `PointwiseEq` — Prop definition (no equation lemmas)
* `PointwiseEq.refl` — `fun _ => Eq.refl _`
* `RawTermSubst.lift_pointwise` — Fin pattern match on 0 / k+1
  (per `feedback_lean_fin_cases_axiom` — direct `⟨0, _⟩` / `⟨k+1, _⟩`
  structure matching is axiom-clean)
* `iterateLiftRaw_RawTermSubst_pointwise` — Nat induction (`zero` /
  `succ`)
* `RawTerm.subst_pointwise` / `RawTermChildren.subst_pointwise` —
  mutual structural match on `RawTerm` / `RawTermChildren`
  (full-enum, no wildcards), with binary `by_cases hVar` on
  `Generator`'s `DecidableEq` (which is propext-free —
  `instDecidableEqGenerator`)

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — The pointwise-equality predicate

We avoid funext by carrying pointwise equality as a Prop-valued
relation throughout the Action-law machinery.  Concrete instances
(`RawTermSubst.identity`, `RawTermSubst.compose`, etc.) prove
pointwise relationships via this predicate rather than via function
equality.
-/

/-- Pointwise equality of substitutions.

Two substitutions agree pointwise when they produce the same
substituent for every variable position.  This is the propositional
analog of function equality, sidestepping funext.

Used by `lift_pointwise`, `iterateLiftRaw_pointwise`, and
`RawTerm.subst_pointwise` to thread agreement through binder
crossings and recursive structure. -/
def RawTermSubst.PointwiseEq {sourceScope targetScope : Nat}
    (firstSubstitution secondSubstitution :
        RawTermSubst sourceScope targetScope) : Prop :=
  ∀ position : Fin sourceScope,
    firstSubstitution position = secondSubstitution position

/-- Pointwise equality is reflexive: every substitution agrees with
itself at every position. -/
theorem RawTermSubst.PointwiseEq.refl {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope) :
    RawTermSubst.PointwiseEq someSubstitution someSubstitution :=
  fun _ => Eq.refl _

/-! ## Section 2 — Binder lifts respect pointwise equality

These two lemmas thread `PointwiseEq` through the binder crossings
fold performs.  `lift_pointwise` handles a single binder;
`iterateLiftRaw_RawTermSubst_pointwise` handles arbitrary depths
(needed for generators like `lam` that bind one variable, plus any
future generators that bind multiple). -/

/-- Lifting respects pointwise equality.

Given two substitutions that agree on every source position, their
single-binder lifts agree on every position in the extended scope.

* Variable 0 in the lifted scope: both lifts produce the same fresh
  `gen_var 0` term (definitional, closes by `rfl`).
* Variable k+1 in the lifted scope: both lifts produce
  `RawTerm.weaken (sigma_i ⟨k, _⟩)`; congruence of `weaken` over
  the pointwise hypothesis closes the goal via `rw`. -/
theorem RawTermSubst.lift_pointwise {sourceScope targetScope : Nat}
    {firstSubstitution secondSubstitution :
        RawTermSubst sourceScope targetScope}
    (substEq :
        RawTermSubst.PointwiseEq firstSubstitution secondSubstitution) :
    RawTermSubst.PointwiseEq
        firstSubstitution.lift
        secondSubstitution.lift := by
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨priorPositionValue + 1, hBound⟩ =>
      show RawTerm.weaken
              (firstSubstitution
                  ⟨priorPositionValue, Nat.lt_of_succ_lt_succ hBound⟩) =
            RawTerm.weaken
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
theorem iterateLiftRaw_RawTermSubst_pointwise {sourceScope targetScope : Nat}
    {firstSubstitution secondSubstitution :
        RawTermSubst sourceScope targetScope}
    (substEq :
        RawTermSubst.PointwiseEq firstSubstitution secondSubstitution)
    (binderDepth : Nat) :
    RawTermSubst.PointwiseEq
        (iterateLiftRaw firstSubstitution binderDepth)
        (iterateLiftRaw secondSubstitution binderDepth) := by
  induction binderDepth with
  | zero => exact substEq
  | succ _priorDepth priorIH =>
      exact RawTermSubst.lift_pointwise priorIH

/-! ## Section 3 — The Allais extensionality theorem (mutual induction)

A single mutual structural induction with four arms total — adding
a new Generator requires NO new arm.

The proof uses `by_cases` on Generator's `DecidableEq` (propext-free)
to dispatch between the variable and non-variable arms
of fold.  Both branches are taken simultaneously on both sides of
the equation because the dispatch depends only on the term (not the
substitution), so the two sides always agree on which arm to take. -/

mutual

/-- Allais extensionality: pointwise-equal substitutions produce
equal subst results on any term.

Adding a new Generator does NOT require adding a new arm here — the
proof closes uniformly through the non-variable case via the children
spine recursion. -/
theorem RawTerm.subst_pointwise {sourceScope targetScope : Nat}
    {firstSubstitution secondSubstitution :
        RawTermSubst sourceScope targetScope}
    (substEq :
        RawTermSubst.PointwiseEq firstSubstitution secondSubstitution)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm.subst firstSubstitution sourceTerm =
      RawTerm.subst secondSubstitution sourceTerm := by
  match sourceTerm with
  | .mkGen someGenerator somePayload someChildren =>
    by_cases hVar : someGenerator = .gen_var
    case pos =>
      -- Variable arm: subst reduces to `varToRawTerm sigma_i payload`
      -- which is `sigma_i payload` for RawTermSubst's
      -- ActsOnRawTermVar instance.  The pointwise hypothesis closes
      -- the goal directly.
      subst hVar
      -- After subst, somePayload : Generator.payload .gen_var sourceScope
      -- which is Fin sourceScope by Generator.payload's defn at .gen_var.
      -- fold dispatches the `if hVar : .gen_var = .gen_var` to the
      -- pos branch via Generator.decEq's canonical isTrue, and the
      -- Eq.rec cast reduces to identity since the equality is rfl.
      show ActsOnRawTermVar.varToRawTerm firstSubstitution somePayload =
            ActsOnRawTermVar.varToRawTerm secondSubstitution somePayload
      -- For RawTermSubst's ActsOnRawTermVar instance:
      -- varToRawTerm sigma pos = sigma pos
      exact substEq somePayload
    case neg =>
      -- Non-variable arm: subst reduces to `algebra g (cast payload)
      -- (foldChildren sigma_i children)`.  The algebra and the cast
      -- payload are sigma-independent; only the folded children differ.
      -- The children IH (mutual) closes the goal.
      --
      -- CRITICAL: use `dsimp only [fold]` rather than `unfold fold`.
      -- `unfold` on a mutual recursive def pulls `Quot.sound` via the
      -- equation lemma generation pipeline (see
      -- feedback_lean_unfold_mutual_quot_sound).
      -- `dsimp only` uses definitional reduction without the equation
      -- lemma engine, keeping the proof zero-axiom.
      show RawTerm.subst firstSubstitution
              (.mkGen someGenerator somePayload someChildren) =
            RawTerm.subst secondSubstitution
              (.mkGen someGenerator somePayload someChildren)
      dsimp only [RawTerm.subst, fold]
      simp only [dif_neg hVar]
      congr 1
      exact RawTermChildren.subst_pointwise substEq someChildren

/-- Allais extensionality on children spines: pointwise-equal
substitutions produce equal foldChildren results.

The mutual structure of RawTerm / RawTermChildren means children
get their own pointwise theorem, invoked by the non-variable arm of
subst_pointwise. -/
theorem RawTermChildren.subst_pointwise
    {sourceScope targetScope : Nat}
    {firstSubstitution secondSubstitution :
        RawTermSubst sourceScope targetScope}
    (substEq :
        RawTermSubst.PointwiseEq firstSubstitution secondSubstitution)
    {binderShifts : List Nat}
    (someChildren : RawTermChildren binderShifts sourceScope) :
    RawTermChildren.subst firstSubstitution someChildren =
      RawTermChildren.subst secondSubstitution someChildren := by
  match binderShifts, someChildren with
  | [], .childNil =>
      -- Empty spine: both sides reduce to .childNil by foldChildren's
      -- nil arm.
      rfl
  | headShift :: _, .childCons childHead childTail =>
      -- Cons spine: head is lifted by headShift, tail unchanged.
      -- Both head and tail subst differ between sigma1 and sigma2, so
      -- we apply the IHs on both, threading the pointwise-eq through
      -- iterateLiftRaw for the head.
      show RawTermChildren.childCons
              (RawTerm.subst
                  (iterateLiftRaw firstSubstitution headShift) childHead)
              (RawTermChildren.subst firstSubstitution childTail) =
            RawTermChildren.childCons
              (RawTerm.subst
                  (iterateLiftRaw secondSubstitution headShift) childHead)
              (RawTermChildren.subst secondSubstitution childTail)
      have headEqualityWitness :=
        RawTerm.subst_pointwise
          (iterateLiftRaw_RawTermSubst_pointwise substEq headShift)
          childHead
      have tailEqualityWitness :=
        RawTermChildren.subst_pointwise substEq childTail
      rw [headEqualityWitness, tailEqualityWitness]

end -- mutual

/-! ## Section 4 — Smoke tests

Verify the headline `RawTerm.subst_pointwise` invokes cleanly on
representative terms.

These are sanity checks — the real consumers are
`subst_identity_apply` (which uses `subst_pointwise` to bridge
between the literal `identity` and `iterateLiftRaw identity n`) and
`subst_compose` (similarly). -/

/-- Smoke test: subst_pointwise on `.gen_unit` is `rfl` (the term has
no variables, so no pointwise-eq usage).

Demonstrates that `subst_pointwise` is well-typed and reduces on
closed inputs. -/
theorem RawTerm.subst_pointwise_unit_smoke {scope : Nat}
    {firstSubstitution secondSubstitution :
        RawTermSubst scope scope}
    (substEq :
        RawTermSubst.PointwiseEq firstSubstitution secondSubstitution) :
    RawTerm.subst firstSubstitution
        (.mkGen .gen_unit () .childNil : RawTerm scope) =
      RawTerm.subst secondSubstitution
        (.mkGen .gen_unit () .childNil : RawTerm scope) :=
  RawTerm.subst_pointwise substEq _

/-- Smoke test: subst_pointwise on `.gen_var` uses the pointwise
hypothesis at the variable's position.

Exercises the variable arm of the mutual induction. -/
theorem RawTerm.subst_pointwise_var_smoke {scope : Nat}
    {firstSubstitution secondSubstitution :
        RawTermSubst (scope + 1) (scope + 1)}
    (substEq :
        RawTermSubst.PointwiseEq firstSubstitution secondSubstitution) :
    RawTerm.subst firstSubstitution
        (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
                .childNil) =
      RawTerm.subst secondSubstitution
        (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
                .childNil) :=
  RawTerm.subst_pointwise substEq _

end FX1Poly.Core
