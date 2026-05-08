import LeanFX2.Confluence.ChurchRosser

/-! # Confluence/ConvTrans — typed Conv.trans corollaries

This file collects the typed-level transitivity theorems for the
`Conv` (`∃-StepStar`) relation.  Two shippable layers, in order of
dependency:

## Layer 1 — chain-composition (zero-axiom, shipped here)

When both convertibility witnesses can be produced as explicit
`StepStar` chains (i.e., one endpoint is the StepStar target of
the other), transitivity is direct chain composition via
`StepStar.append` packaged as `Conv.fromStepStar`.  This is the
**monotonic-direction** fragment of trans — every step goes from
source towards target.  Already lives in `Reduction/Conv.lean` as
`Conv.transChains`; re-exposed here for canonical discoverability.

## Layer 2 — full Conv.trans (Phase 7 close-out, partially blocked)

`Conv.trans firstConv secondConv : Conv source target` where each
`Conv` brings its OWN midpoint.  Concretely:

```
Conv source middle  ⇒  ∃ joinA, StepStar source joinA ∧ StepStar middle joinA
Conv middle target  ⇒  ∃ joinB, StepStar middle joinB ∧ StepStar target joinB
```

We need a typed `joinAB` reachable from both `joinA` and `joinB`.
The classical proof uses **typed confluence at `middle`**: given two
typed StepStar chains from `middle` to `joinA` / `joinB`, produce a
typed common reduct `joinAB`.  Then `StepStar source joinAB` (via
`StepStar.append sourceToJoinA joinAToJoinAB`) and `StepStar target
joinAB` (analogously) give us `Conv source target`.

**The blocker**: typed `Step.parStar.confluence` (or `StepStar.
confluence`) requires lifting the raw common reduct to a typed
Term.  The raw common reduct (`RawTerm.cd middleRaw` in lean-fx-2's
construction) needs a typed inhabitant at `middleType` (or some
closed-type-aligned reduct).  Constructing the typed inhabitant
requires inverting every `RawStep.par` constructor against the
typed source — which IS the strong subject-reduction theorem.

What's shipped today vs blocked:

* **Type preservation under reduction** (M06/M07, type EQUALITY):
  `Step.preserves_isClosedTy`, `Step.preserves_ty_arrow / list /
  option / either / empty / interval / equiv / record / codata /
  modal` (in `Term/SubjectReductionGeneral.lean`).  These say
  "if the source has a closed type, so does the target" — but
  they output a Ty equation, NOT a typed Term construction.
* **Strong SR (term construction)**: NOT shipped.  Required for
  full typed confluence and hence full typed `Conv.trans`.

`Conv.transRaw` (in `Confluence/ChurchRosser.lean`) ships the
raw-output flavor: typed inputs, raw common reduct.  Sufficient for
Layer 9 decidable conversion; insufficient for re-injecting into
typed Conv.

## What this file ships

* `Conv.trans_via_chains` — Layer 1 chain composition (alias of
  `Conv.transChains` for canonical discoverability under the
  Confluence module hierarchy).
* `Conv.trans_chainLeft` — given `StepStar source middle` and
  `Conv middle target`, produce `Conv source target` by pre-pending
  the chain to the second Conv's source-side chain.  Zero-axiom:
  re-uses the second Conv's existing midpoint as the join.
* `Conv.trans_chainRight` — given `Conv source middle` and a
  **reverse** chain `target →* middle`, produce `Conv source
  target`.  Symmetric to `trans_chainLeft`: append the reverse
  chain to the first Conv's middle-side chain.  Zero-axiom.
* `Conv.trans_step_left` — single-step variant of `trans_chainLeft`.
* `Conv.trans_step_right` — single-step variant of
  `trans_chainRight` (reverse step).
* `Conv.trans_fromStepLeft` / `Conv.trans_fromStepRight` —
  Conv-Step composition collapsed.
* `Conv.trans_refl_left` / `Conv.trans_refl_right` — degenerate
  cases when one input is implicitly `Conv.refl`-shaped.

These variants are real subsets of full `Conv.trans` — each works
without strong subject reduction by exploiting the asymmetric
chain structure.

The **forward** flavor `trans_chainRightForward` (Conv on the left,
forward chain on the right) is NOT shippable: it requires reversing
a `StepStar`, which is the same wall as full `Conv.trans`.  Use
`trans_chainRight` (reverse chain) when applicable.

## Subject reduction term construction — what's still pending

The fully unrestricted `Conv.trans` (where each Conv brings its
own midpoint and we must construct a typed Term at the raw common
reduct) remains blocked on strong subject reduction with term
construction.  M06/M07 ship the type-EQUALITY part — given a
closed-typed source, the target also has the same closed type —
but they do NOT construct a typed `Term context closedType
targetRaw` from the raw step.

The simplest typed-construction targets (closed-type ι reduction
rules like `Step.iotaBoolElimTrue`/`Step.iotaNatElimZero` whose
target Term is supplied to the constructor itself) are structurally
trivial — the typed term lives directly in the Step.par witness.
But the general construction at *every* raw step shape requires
inverting each `RawStep.par` ctor against an arbitrary typed
source, which is the ~100-case enterprise this file's docstring
documents.

## Future work: full Conv.trans (Phase 7 D5–D8)

Shipping the full `Conv.trans` requires one of:

1. **Strong typed SR** — inversion-based construction of typed
   Step.par from raw Step.par at typed sources.  Shape:
   ```
   theorem Step.par.fromRaw_at_typed
       {sourceTerm : Term context tipe sourceRaw}
       (rawStep : RawStep.par sourceRaw targetRaw) :
       ∃ targetTipe targetTerm,
         Step.par sourceTerm (targetTerm : Term context targetTipe targetRaw)
   ```
   Approximately one case per `RawStep.par` constructor (~100+
   cases).  At closed types, the Ty index is preserved per M06/M07;
   open types need richer Ty inversion machinery.

2. **Typed cd construction** — given `m : Term context ty raw`,
   produce `cdTerm : Term context cdTy (RawTerm.cd raw)` and
   `Step.par m cdTerm`.  Equivalent in strength to (1).

3. **Closed-type restriction** — ship a variant
   `Conv.trans_at_isClosedTy` that requires `IsClosedTy middleType`.
   Even this needs a typed cd construction at closed types
   (per the type-preservation part of (1)/(2) above), which is not
   itself shippable from M06/M07 alone.

The dependency chain `M06 ⇒ Conv.trans` claimed in the v2 roadmap
is incomplete — M06 is **necessary** for type alignment in the
proof, but **not sufficient** for term construction.  Strong SR
(Phase 7 close-out item) is the missing prerequisite.

## Dependencies

* `Confluence/ChurchRosser.lean` — `Conv.transRaw`, `RawStep.parStar.confluence`
* `Reduction/Conv.lean` — `Conv` definition, `Conv.transChains`
* `Reduction/StepStar.lean` — `StepStar.append`
-/

namespace LeanFX2

/-- **Chain-composition transitivity** for typed `Conv`.  Alias of
`Conv.transChains` exposing it under the `Confluence` namespace
hierarchy alongside `Conv.transRaw` / `Conv.canonicalForm`.

Given explicit `StepStar` chains `source →* middle →* target`,
produce `Conv source target` directly via `StepStar.append` packaged
as `Conv.fromStepStar`.  No confluence required: the path is
monotonic from source to target without crossing through a common
reduct.

Use this when you can produce explicit chain witnesses.  When the
Conv inputs bring their OWN midpoints (the general case), the full
`Conv.trans` is needed and is currently blocked on strong subject
reduction (Phase 7 close-out — see file docstring). -/
theorem Conv.trans_via_chains
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstChain : StepStar sourceTerm middleTerm)
    (secondChain : StepStar middleTerm targetTerm) :
    Conv sourceTerm targetTerm :=
  Conv.transChains firstChain secondChain

/-! ## Asymmetric trans variants — Phase 2 shippable subsets

The full `Conv.trans` (where each Conv brings its own midpoint)
requires strong subject reduction with term construction.  But
**asymmetric** flavors — where one side is an explicit `StepStar`
chain and the other is a `Conv` — are shippable directly.

* `trans_chainLeft`: chain on the left + Conv on the right.  We
  pre-pend the chain to the second Conv's source-side chain via
  `StepStar.append`; the second Conv's midpoint becomes the new
  midpoint.  No confluence call needed.
* `trans_chainRightForward`: Conv on the left + chain on the
  right.  Symmetric: post-pend the chain to the first Conv's
  target-side chain.

Both compose existing chain machinery — the typed midpoint is
inherited from the input `Conv`'s existential, never constructed. -/

/-- **Chain on the left**, Conv on the right.

Given an explicit chain `source →* middle` and a `Conv middle
target` whose midpoint is some typed `joinPoint`, produce
`Conv source target` by:

1. Extracting the second Conv's midpoint and the chains
   `middle →* joinPoint` and `target →* joinPoint`.
2. Pre-pending the input chain `source →* middle` to the
   midpoint chain via `StepStar.append`, yielding
   `source →* joinPoint`.
3. Re-packaging as `Conv source target` with the same
   `joinPoint` as the new midpoint.

No confluence required: the typed midpoint is inherited from
the input `Conv`. -/
theorem Conv.trans_chainLeft
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstChain : StepStar sourceTerm middleTerm)
    (secondConv : Conv middleTerm targetTerm) :
    Conv sourceTerm targetTerm := by
  obtain ⟨joinType, joinRaw, joinTerm,
          middleToJoin, targetToJoin⟩ := secondConv
  exact ⟨joinType, joinRaw, joinTerm,
         StepStar.append firstChain middleToJoin,
         targetToJoin⟩

/-! ### Note: forward `trans_chainRightForward` is structurally blocked

A naive `Conv source middle ⟶ StepStar middle target ⟶ Conv source
target` flavor cannot be shipped without strong subject reduction.
The first `Conv` has internal midpoint `joinA` with `source →* joinA`
and `middle →* joinA`.  To ship `Conv source target` we need a
common reduct reachable from both `source` and `target`.

* If we choose `joinA` as the new midpoint: `source →* joinA` is
  given, but `target →* joinA` would require a *reverse* of
  `middle →* target` (so `target →* middle`) appended with
  `middle →* joinA`.  `StepStar` is not symmetric.
* If we choose `target` as the new midpoint: `target →* target`
  is `refl`, but `source →* target` would require `source →*
  middle` first (reverse of `source →* joinA` and `middle →* joinA`
  not adjacent).

Hence forward-chain-on-right is exactly the case that needs
typed confluence at `joinA` — the same wall as full
`Conv.trans`.  Use `Conv.trans_chainRight` (reverse-chain) when
the target really is a reduct of `middle`. -/

/-- **Conv on the left**, **reverse** chain on the right.

Given `Conv source middle` and a *reverse* chain `target →*
middle`, produce `Conv source target`.  Symmetric to
`trans_chainLeft`.

Strategy: extract the first Conv's midpoint and chains, then
build:
* Source-side: `source →* joinA` (given by first Conv).
* Target-side: `target →* middle →* joinA` via
  `StepStar.append` of the reverse chain with the first Conv's
  middle-side chain.

No confluence required. -/
theorem Conv.trans_chainRight
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstConv : Conv sourceTerm middleTerm)
    (reverseChain : StepStar targetTerm middleTerm) :
    Conv sourceTerm targetTerm := by
  obtain ⟨joinType, joinRaw, joinTerm,
          sourceToJoin, middleToJoin⟩ := firstConv
  exact ⟨joinType, joinRaw, joinTerm,
         sourceToJoin,
         StepStar.append reverseChain middleToJoin⟩

/-! ## Single-step variants

When the chain is a single `Step`, lifting through `StepStar.fromStep`
gives the same theorem with one step instead of a chain. -/

/-- Single-step variant of `trans_chainLeft`. -/
theorem Conv.trans_step_left
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstStep : Step sourceTerm middleTerm)
    (secondConv : Conv middleTerm targetTerm) :
    Conv sourceTerm targetTerm :=
  Conv.trans_chainLeft (StepStar.fromStep firstStep) secondConv

/-- Single-step variant of `trans_chainRight` (reverse chain). -/
theorem Conv.trans_step_right
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstConv : Conv sourceTerm middleTerm)
    (reverseStep : Step targetTerm middleTerm) :
    Conv sourceTerm targetTerm :=
  Conv.trans_chainRight firstConv (StepStar.fromStep reverseStep)

/-! ## Trivial transitivity at refl

When one of the input Convs is built via `Conv.refl` (i.e., its
endpoints are the same term), trans degenerates to the other
input.  Mostly used for cleaning up trivial proof obligations. -/

/-- `Conv.trans` where the first Conv is `refl`: result is the
second Conv (after specializing the implicit indices). -/
theorem Conv.trans_refl_left
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {middleType targetType : Ty level scope}
    {middleRaw targetRaw : RawTerm scope}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (secondConv : Conv middleTerm targetTerm) :
    Conv middleTerm targetTerm :=
  secondConv

/-- `Conv.trans` where the second Conv is `refl`: result is the
first Conv (after specializing the implicit indices). -/
theorem Conv.trans_refl_right
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType : Ty level scope}
    {sourceRaw middleRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    (firstConv : Conv sourceTerm middleTerm) :
    Conv sourceTerm middleTerm :=
  firstConv

/-! ## Step variants — direct corollaries of `Conv.fromStep`

When you have a `Step source target` and want to compose with an
adjacent `Conv`, the easiest path is:

* `Conv.fromStep step` produces `Conv source target` directly.
* Then `Conv.trans_chainLeft` / `Conv.trans_chainRight` (or
  their step variants above) compose with adjacent Convs.

These corollaries collapse common compositions. -/

/-- `Step source middle` and `Conv middle target` give `Conv source
target`.  Pure existential composition; no confluence. -/
theorem Conv.trans_fromStepLeft
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstStep : Step sourceTerm middleTerm)
    (secondConv : Conv middleTerm targetTerm) :
    Conv sourceTerm targetTerm :=
  Conv.trans_step_left firstStep secondConv

/-- `Conv source middle` and reverse `Step target middle` give
`Conv source target`. -/
theorem Conv.trans_fromStepRight
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstConv : Conv sourceTerm middleTerm)
    (reverseStep : Step targetTerm middleTerm) :
    Conv sourceTerm targetTerm :=
  Conv.trans_step_right firstConv reverseStep

end LeanFX2
