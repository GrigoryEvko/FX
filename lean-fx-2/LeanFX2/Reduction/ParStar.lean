import LeanFX2.Reduction.ParRed

/-! # Reduction/ParStar — reflexive-transitive closure of Step.par

`Step.parStar source target : Prop` is the multi-step parallel-
reduction relation.  Each chain step is a `Step.par` connecting
two typed `Term`s whose contexts agree but whose source/target
types and raw indices may differ.

This is the typed counterpart to `RawStep.parStar` (Layer 3 raw).
The bridge `Step.parStar.toRawBridge` projects a typed parallel
chain to a raw parallel chain, where Phase 6.C confluence applies.

## Constructors

* `refl term` — zero parallel-steps (term reduces to itself).
* `trans firstStep restChain` — one parallel step, then the
  chain continues.

## Operations

* `Step.par.toStar` — embed single-step into multi-step.
* `Step.parStar.snoc` — append a single Step.par at the end.
* `Step.parStar.append` — concatenate two chains.

## Why this isn't just StepStar (single-step closure)

`StepStar` chains *single* `Step` reductions (one redex per step).
`parStar` chains *parallel* `Step.par` reductions (all redexes
simultaneously per step).  Both have the same RT closure — that's
why the diamond proof works on `Step.par` and lifts to `StepStar`.
-/

namespace LeanFX2

/-- Reflexive-transitive closure of `Step.par`.  Multi-step
parallel reduction.  Source/target types and raw indices may
shift across steps; only the context is fixed. -/
inductive Step.parStar :
    ∀ {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {sourceType targetType : Ty level scope}
      {sourceRaw targetRaw : RawTerm scope},
      Term context sourceType sourceRaw →
      Term context targetType targetRaw →
      Prop
  /-- Reflexivity: any term parallel-reduces to itself in zero steps. -/
  | refl {mode level scope} {context : Ctx mode level scope}
      {someType : Ty level scope} {someRaw : RawTerm scope}
      (someTerm : Term context someType someRaw) :
      Step.parStar someTerm someTerm
  /-- Transitivity: prepend a single `Step.par` to a chain. -/
  | trans {mode level scope} {context : Ctx mode level scope}
      {firstType middleType targetType : Ty level scope}
      {firstRaw middleRaw targetRaw : RawTerm scope}
      {firstTerm : Term context firstType firstRaw}
      {middleTerm : Term context middleType middleRaw}
      {targetTerm : Term context targetType targetRaw} :
      Step.par firstTerm middleTerm →
      Step.parStar middleTerm targetTerm →
      Step.parStar firstTerm targetTerm

/-- Embed a single parallel step into the reflexive-transitive
closure (one-step chain). -/
theorem Step.par.toStar
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    Step.parStar sourceTerm targetTerm :=
  Step.parStar.trans parallelStep (Step.parStar.refl _)

/-- Append a single parallel step at the end of a chain. -/
theorem Step.parStar.snoc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstType middleType targetType : Ty level scope}
    {firstRaw middleRaw targetRaw : RawTerm scope}
    {firstTerm : Term context firstType firstRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (chain : Step.parStar firstTerm middleTerm)
    (parallelStep : Step.par middleTerm targetTerm) :
    Step.parStar firstTerm targetTerm := by
  induction chain with
  | refl _ => exact parallelStep.toStar
  | trans firstStep _ restIH =>
      exact Step.parStar.trans firstStep (restIH parallelStep)

/-- Concatenate two parallel chains sharing a midpoint. -/
theorem Step.parStar.append
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {firstType middleType targetType : Ty level scope}
    {firstRaw middleRaw targetRaw : RawTerm scope}
    {firstTerm : Term context firstType firstRaw}
    {middleTerm : Term context middleType middleRaw}
    {targetTerm : Term context targetType targetRaw}
    (firstChain : Step.parStar firstTerm middleTerm)
    (secondChain : Step.parStar middleTerm targetTerm) :
    Step.parStar firstTerm targetTerm := by
  induction firstChain with
  | refl _ => exact secondChain
  | trans firstStep _ restIH =>
      exact Step.parStar.trans firstStep (restIH secondChain)

end LeanFX2
