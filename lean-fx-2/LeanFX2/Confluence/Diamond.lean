import LeanFX2.Confluence.RawDiamond
import LeanFX2.Bridge

/-! # Diamond — TODO POLYCELL: BODY DISABLED

Body depends on cd_lemma / Conv.canonical_form / parStar.confluence /
RawStep.parStar orchestration deleted in commit c2efaccf (cascade-fake
bulldoze).  Replacement: FXcdLemma / FXConv view defs per polycell.md §5.
Imports are preserved at top so downstream transitive imports still work.
-/

/- TODO POLYCELL: original body preserved as block comment


/-! # Confluence/Diamond — diamond corollaries for typed parallel reduction

Diamond at the raw level (`RawStep.par.diamond`, shipped in
`Confluence/RawDiamond.lean`) lifts to a typed corollary via the
typed→raw bridge `Step.par.toRawBridge`.

## Typed-input, raw-output diamond

```lean
theorem Step.par.diamondRaw
    {sourceTerm leftTarget rightTarget : ...}
    (leftStep : Step.par sourceTerm leftTarget)
    (rightStep : Step.par sourceTerm rightTarget) :
    ∃ commonRaw,
      RawStep.par leftRaw commonRaw ∧
      RawStep.par rightRaw commonRaw
```

Both typed inputs project to raw via `Step.par.toRawBridge`, then
`RawStep.par.diamond` produces the common raw reduct.

## Why not a typed-output diamond?

A typed-output diamond would deliver `∃ (commonType : Ty)
(commonRaw : RawTerm) (commonTerm : Term context commonType
commonRaw), Step.par leftTarget commonTerm ∧ Step.par rightTarget
commonTerm`.  Constructing the typed `commonTerm` requires subject
reduction for `Step.par`: given a parallel-reduction step from a
well-typed `leftTarget`, we must produce a Ty for the further
reduct that lands at the common raw form.  Subject reduction is
M05/M06 work (planned Phase 7) — only the `IsClosedTy` family
(M07) is shipped at present, which doesn't cover the arrow-typed
β-redex case.

Until subject reduction lands, the strongest typed-input diamond
shippable is the raw-output corollary above.  Layer 9 (decidable
conversion) and the elaborator's coherence proofs consume the raw
form directly: typed convertibility is preserved by typing
(elaboration-time invariant), so once two reducts agree at the
raw level, their original typed terms are convertible by
construction.

## What this file ships (zero axioms)

* `Step.par.diamondRaw` — typed inputs, raw common reduct, single-step
* `Step.par.diamondRawSingle` — alias matching the predecessor's
  `cd`-based proof shape (uses `RawTerm.cd` as the join witness)

## Dependencies

* `Confluence/RawDiamond.lean` — `RawStep.par.diamond` shipped
* `Bridge.lean` — `Step.par.toRawBridge` shipped

## Downstream consumers

* `Confluence/ChurchRosser.lean` — multi-step typed-input
  confluence via raw output
* `Algo/DecConv.lean` — decidable conversion uses raw join
-/

namespace LeanFX2

/-- **Typed-input, raw-output diamond** for `Step.par`.

If `sourceTerm` parallel-reduces to both `leftTarget` and
`rightTarget` (each typed potentially differently), then their raw
projections share a common raw reduct reachable by single
parallel steps.

The raw common reduct is `RawTerm.cd sourceTerm.toRaw` in lean-fx-2's
construction (per `RawStep.par.diamond` from the cd-domination
chain).  Lifting back to a typed common Term requires subject
reduction — see file docstring. -/
theorem Step.par.diamondRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType leftType rightType : Ty level scope}
    {sourceRaw leftRaw rightRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {leftTarget : Term context leftType leftRaw}
    {rightTarget : Term context rightType rightRaw}
    (leftStep : Step.par sourceTerm leftTarget)
    (rightStep : Step.par sourceTerm rightTarget) :
    ∃ commonRaw,
      RawStep.par leftRaw commonRaw ∧
      RawStep.par rightRaw commonRaw :=
  RawStep.par.diamond
    (Step.par.toRawBridge leftStep)
    (Step.par.toRawBridge rightStep)

/-- Alias of `Step.par.diamondRaw` exposing the cd-based join
witness.  By construction `RawStep.par.diamond` chooses
`RawTerm.cd sourceRaw` as the common reduct. -/
theorem Step.par.diamondRawCd
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType leftType rightType : Ty level scope}
    {sourceRaw leftRaw rightRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {leftTarget : Term context leftType leftRaw}
    {rightTarget : Term context rightType rightRaw}
    (leftStep : Step.par sourceTerm leftTarget)
    (rightStep : Step.par sourceTerm rightTarget) :
    RawStep.par leftRaw (RawTerm.cd sourceRaw) ∧
    RawStep.par rightRaw (RawTerm.cd sourceRaw) :=
  ⟨RawStep.par.cd_lemma (Step.par.toRawBridge leftStep),
   RawStep.par.cd_lemma (Step.par.toRawBridge rightStep)⟩

end LeanFX2

-/
