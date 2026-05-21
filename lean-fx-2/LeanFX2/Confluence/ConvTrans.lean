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

/-! ## Asymmetric typed Conv-trans → raw join projections

When a consumer takes the typed asymmetric trans variants
(`Conv.trans_chainLeft` / `Conv.trans_chainRight` /
`Conv.trans_step_left` / `Conv.trans_step_right`) and immediately
projects the resulting typed Conv to a raw join via
`Conv.canonicalRaw`, the composition is a one-line corollary.
Shipping these saves the intermediate typed-Conv binding at call
sites that ultimately want raw output (e.g., bridges to
`RawStep.parStar.confluence`-based downstream work).

Each corollary is `Conv.canonicalRaw ∘ Conv.trans_<asymmetric>`. -/

/-- Raw-join projection of `Conv.trans_chainLeft`.

Given `StepStar source middle` and `Conv middle target`, produce a
raw common reduct reachable from both `sourceRaw` and `targetRaw`.
The chain is prepended to the second Conv's source-side chain via
`StepStar.append` (no confluence required — the typed midpoint is
inherited from the input Conv). -/
theorem Conv.transRaw_chainLeft
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstChain : StepStar sourceTerm middleTerm)
    (secondConv : Conv middleTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw :=
  Conv.canonicalRaw (Conv.trans_chainLeft firstChain secondConv)

/-- Raw-join projection of `Conv.trans_chainRight`.

Given `Conv source middle` and a *reverse* chain `target →* middle`,
produce a raw join.  Symmetric to `transRaw_chainLeft`. -/
theorem Conv.transRaw_chainRight
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstConv : Conv sourceTerm middleTerm)
    (reverseChain : StepStar targetTerm middleTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw :=
  Conv.canonicalRaw (Conv.trans_chainRight firstConv reverseChain)

/-- Raw-join projection of `Conv.trans_step_left`.  Single-step
variant of `Conv.transRaw_chainLeft`. -/
theorem Conv.transRaw_stepLeft
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstStep : Step sourceTerm middleTerm)
    (secondConv : Conv middleTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw :=
  Conv.canonicalRaw (Conv.trans_step_left firstStep secondConv)

/-- Raw-join projection of `Conv.trans_step_right`.  Single-step
variant of `Conv.transRaw_chainRight` (reverse direction). -/
theorem Conv.transRaw_stepRight
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstConv : Conv sourceTerm middleTerm)
    (reverseStep : Step targetTerm middleTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw :=
  Conv.canonicalRaw (Conv.trans_step_right firstConv reverseStep)

/-! ## Two-chain / two-step → raw join projections

The symmetric counterparts to the asymmetric variants above:
when both sides are already chains (or single steps), we don't need
to package one through `Conv` first.  `Conv.transChains` produces a
`Conv` directly via `StepStar.append`; the raw projection follows
by `Conv.canonicalRaw`. -/

/-- Two chains `source →* middle →* target` give a raw common
reduct reachable from both `sourceRaw` and `targetRaw`. -/
theorem Conv.transRaw_chains
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstChain : StepStar sourceTerm middleTerm)
    (secondChain : StepStar middleTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw :=
  Conv.canonicalRaw (Conv.transChains firstChain secondChain)

/-- Two single steps `source ⟶ middle ⟶ target` give a raw common
reduct.  Both are lifted to chains via `StepStar.fromStep` and
composed via `Conv.transChains`. -/
theorem Conv.transRaw_twoSteps
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstStep : Step sourceTerm middleTerm)
    (secondStep : Step middleTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw :=
  Conv.canonicalRaw
    (Conv.transChains (StepStar.fromStep firstStep)
                      (StepStar.fromStep secondStep))

/-- A chain followed by a single step `source →* middle ⟶ target`
gives a raw common reduct. -/
theorem Conv.transRaw_chainStep
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstChain : StepStar sourceTerm middleTerm)
    (secondStep : Step middleTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw :=
  Conv.canonicalRaw
    (Conv.transChains firstChain (StepStar.fromStep secondStep))

/-- A single step followed by a chain `source ⟶ middle →* target`
gives a raw common reduct. -/
theorem Conv.transRaw_stepChain
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstStep : Step sourceTerm middleTerm)
    (secondChain : StepStar middleTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw :=
  Conv.canonicalRaw
    (Conv.transChains (StepStar.fromStep firstStep) secondChain)

/-! ## Asymmetric `{chainLeft, chainRight, stepLeft, stepRight}` × action lifters

The four asymmetric trans variants above (`Conv.trans_chainLeft` /
`Conv.trans_chainRight` / `Conv.trans_step_left` / `Conv.trans_step_right`)
package a chain (or step) plus a `Conv` into a typed `Conv source target`
without invoking confluence.  Composing the typed result with the Conv-axis
raw projections (`Conv.renameRaw` / `Conv.weakenRaw` / `Conv.substRaw` /
`Conv.subst0Raw` from `ChurchRosser.lean`) yields 16 one-line raw-join
corollaries — every cell of the (input shape) × (action) grid.

Consumers reach for these whenever they have an asymmetric
chain+Conv input and want a raw join under a structural action (rename,
weaken, subst, subst0) in one call.  Typical downstream sites: transp-
cascade subst-equivariance lemmas and the future Step.eta cong-rule
lifters of Phase F. -/

/-- Raw-rename projection of `Conv.trans_chainLeft`. -/
theorem Conv.transRaw_chainLeft_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType targetType : Ty level sourceScope}
    {sourceRaw middleRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (firstChain : StepStar sourceTerm middleTerm)
    (secondConv : Conv middleTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (targetRaw.rename rawRenaming) commonRaw :=
  Conv.renameRaw rawRenaming (Conv.trans_chainLeft firstChain secondConv)

/-- Canonical-weaken specialization of
`Conv.transRaw_chainLeft_renamed`. -/
theorem Conv.transRaw_chainLeft_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstChain : StepStar sourceTerm middleTerm)
    (secondConv : Conv middleTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar targetRaw.weaken commonRaw :=
  Conv.weakenRaw (Conv.trans_chainLeft firstChain secondConv)

/-- Raw-subst projection of `Conv.trans_chainLeft`. -/
theorem Conv.transRaw_chainLeft_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType targetType : Ty level sourceScope}
    {sourceRaw middleRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (firstChain : StepStar sourceTerm middleTerm)
    (secondConv : Conv middleTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (targetRaw.subst rawSubst) commonRaw :=
  Conv.substRaw rawSubst (Conv.trans_chainLeft firstChain secondConv)

/-- Singleton-substitution specialization of
`Conv.transRaw_chainLeft_substituted`. -/
theorem Conv.transRaw_chainLeft_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType middleType targetType : Ty level (scope + 1)}
    {sourceRaw middleRaw targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (argRaw : RawTerm scope)
    (firstChain : StepStar sourceTerm middleTerm)
    (secondConv : Conv middleTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (targetRaw.subst0 argRaw) commonRaw :=
  Conv.subst0Raw argRaw (Conv.trans_chainLeft firstChain secondConv)

/-- Raw-rename projection of `Conv.trans_chainRight`. -/
theorem Conv.transRaw_chainRight_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType targetType : Ty level sourceScope}
    {sourceRaw middleRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (firstConv : Conv sourceTerm middleTerm)
    (reverseChain : StepStar targetTerm middleTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (targetRaw.rename rawRenaming) commonRaw :=
  Conv.renameRaw rawRenaming (Conv.trans_chainRight firstConv reverseChain)

/-- Canonical-weaken specialization of
`Conv.transRaw_chainRight_renamed`. -/
theorem Conv.transRaw_chainRight_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstConv : Conv sourceTerm middleTerm)
    (reverseChain : StepStar targetTerm middleTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar targetRaw.weaken commonRaw :=
  Conv.weakenRaw (Conv.trans_chainRight firstConv reverseChain)

/-- Raw-subst projection of `Conv.trans_chainRight`. -/
theorem Conv.transRaw_chainRight_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType targetType : Ty level sourceScope}
    {sourceRaw middleRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (firstConv : Conv sourceTerm middleTerm)
    (reverseChain : StepStar targetTerm middleTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (targetRaw.subst rawSubst) commonRaw :=
  Conv.substRaw rawSubst (Conv.trans_chainRight firstConv reverseChain)

/-- Singleton-substitution specialization of
`Conv.transRaw_chainRight_substituted`. -/
theorem Conv.transRaw_chainRight_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType middleType targetType : Ty level (scope + 1)}
    {sourceRaw middleRaw targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (argRaw : RawTerm scope)
    (firstConv : Conv sourceTerm middleTerm)
    (reverseChain : StepStar targetTerm middleTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (targetRaw.subst0 argRaw) commonRaw :=
  Conv.subst0Raw argRaw (Conv.trans_chainRight firstConv reverseChain)

/-- Raw-rename projection of `Conv.trans_step_left`.  Single-step
variant of `Conv.transRaw_chainLeft_renamed`. -/
theorem Conv.transRaw_stepLeft_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType targetType : Ty level sourceScope}
    {sourceRaw middleRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (firstStep : Step sourceTerm middleTerm)
    (secondConv : Conv middleTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (targetRaw.rename rawRenaming) commonRaw :=
  Conv.renameRaw rawRenaming (Conv.trans_step_left firstStep secondConv)

/-- Canonical-weaken specialization of
`Conv.transRaw_stepLeft_renamed`. -/
theorem Conv.transRaw_stepLeft_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstStep : Step sourceTerm middleTerm)
    (secondConv : Conv middleTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar targetRaw.weaken commonRaw :=
  Conv.weakenRaw (Conv.trans_step_left firstStep secondConv)

/-- Raw-subst projection of `Conv.trans_step_left`. -/
theorem Conv.transRaw_stepLeft_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType targetType : Ty level sourceScope}
    {sourceRaw middleRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (firstStep : Step sourceTerm middleTerm)
    (secondConv : Conv middleTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (targetRaw.subst rawSubst) commonRaw :=
  Conv.substRaw rawSubst (Conv.trans_step_left firstStep secondConv)

/-- Singleton-substitution specialization of
`Conv.transRaw_stepLeft_substituted`. -/
theorem Conv.transRaw_stepLeft_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType middleType targetType : Ty level (scope + 1)}
    {sourceRaw middleRaw targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (argRaw : RawTerm scope)
    (firstStep : Step sourceTerm middleTerm)
    (secondConv : Conv middleTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (targetRaw.subst0 argRaw) commonRaw :=
  Conv.subst0Raw argRaw (Conv.trans_step_left firstStep secondConv)

/-- Raw-rename projection of `Conv.trans_step_right`.  Single-reverse-
step variant of `Conv.transRaw_chainRight_renamed`. -/
theorem Conv.transRaw_stepRight_renamed
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType targetType : Ty level sourceScope}
    {sourceRaw middleRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (firstConv : Conv sourceTerm middleTerm)
    (reverseStep : Step targetTerm middleTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (targetRaw.rename rawRenaming) commonRaw :=
  Conv.renameRaw rawRenaming (Conv.trans_step_right firstConv reverseStep)

/-- Canonical-weaken specialization of
`Conv.transRaw_stepRight_renamed`. -/
theorem Conv.transRaw_stepRight_weakened
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType middleType targetType : Ty level scope}
    {sourceRaw middleRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstConv : Conv sourceTerm middleTerm)
    (reverseStep : Step targetTerm middleTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar targetRaw.weaken commonRaw :=
  Conv.weakenRaw (Conv.trans_step_right firstConv reverseStep)

/-- Raw-subst projection of `Conv.trans_step_right`. -/
theorem Conv.transRaw_stepRight_substituted
    {mode : Mode} {level sourceScope targetScope : Nat}
    {context : Ctx mode level sourceScope}
    {sourceType middleType targetType : Ty level sourceScope}
    {sourceRaw middleRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (rawSubst : RawTermSubst sourceScope targetScope)
    (firstConv : Conv sourceTerm middleTerm)
    (reverseStep : Step targetTerm middleTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (targetRaw.subst rawSubst) commonRaw :=
  Conv.substRaw rawSubst (Conv.trans_step_right firstConv reverseStep)

/-- Singleton-substitution specialization of
`Conv.transRaw_stepRight_substituted`. -/
theorem Conv.transRaw_stepRight_subst0
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType middleType targetType : Ty level (scope + 1)}
    {sourceRaw middleRaw targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (argRaw : RawTerm scope)
    (firstConv : Conv sourceTerm middleTerm)
    (reverseStep : Step targetTerm middleTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (targetRaw.subst0 argRaw) commonRaw :=
  Conv.subst0Raw argRaw (Conv.trans_step_right firstConv reverseStep)

/-! ## Cong-rule via Conv chain in closed-type fragment

For `IsClosedTy`-typed terms, every `Step` (and `StepStar`) preserves
the type by `Step.preserves_isClosedTy`.  This means that when we
have a typed Conv between two closed-typed terms, we can ASSUME
that any midpoint of the existential must also have the same closed
type.  This is a property the trans variants exploit.

## Phase 3 building blocks: canonical-head parStar inversions

`RawStep.parStar.unit_inv` (and its boolTrue/boolFalse/natZero/
listNil/optionNone siblings, lifted from `RawStep.par.<head>_inv`
via `canonical_inv_helper` in `Confluence/RawParStarCong.lean`) say:
a parStar chain whose source is a canonical-head raw term reaches
only that same canonical-head raw term.

These are MACHINERY for the eventual `Conv.canonicalForm_<head>`
corollaries — but those corollaries don't ship yet because the
**reverse** direction is FALSE in general.  Concretely:
`RawStep.par source unit → source = unit` is **NOT** a theorem.
Counterexample: `(λx. unit) argument →β unit` — source is the
β-redex, not `unit`.

What this means for typed Conv: given `Conv source target` where
source.toRaw = `RawTerm.unit`, we get `RawStep.parStar source.toRaw
commonRaw` which by `unit_inv` forces commonRaw = `RawTerm.unit`,
so `RawStep.parStar target.toRaw unit`.  This does NOT force
target.toRaw = unit (the β counterexample above is exactly such
a target).  Hence target may be a more complex Term still
convertible to `Term.unit` — which is the `Conv` content already.

So the canonical-head inversions are necessary but not sufficient
for the typed Conv canonical-form theorem.  The missing piece is
the typed lift: from `RawStep.parStar t.toRaw unit` to a typed
`StepStar t (Term.unit ...)`.  That's the SR-with-term-construction
wall.

The inversions still ship as standalone lemmas because they're
useful in other contexts (e.g., decidable conversion via
`Algo/RawWHNF.lean`'s normalizer, where checking that a head
matches a canonical raw form is a primary operation). -/

end LeanFX2
