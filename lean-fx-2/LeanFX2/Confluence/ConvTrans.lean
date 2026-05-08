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

end LeanFX2
