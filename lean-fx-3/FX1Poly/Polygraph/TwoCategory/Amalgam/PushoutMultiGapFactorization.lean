import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutMultiGapSplice
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutRightImageDecision

/-! # Polygraph/TwoCategory/Amalgam/PushoutMultiGapFactorization — the ARBITRARY-ARITY forward splice at a FIXED
wire count, and the honest wall on the wire-CHANGING factorization (WP-AMALG-2 r5, #2043)

`PushoutMultiGapSplice.lean` (r4) shipped `threeGapSpliceConv`: a HARD-CODED three-gap, two-`s`-wall word
(`t·s·t·s·t`) normalized END-TO-END by splicing three per-gap base-case collapses across the two fixed `s`-walls.
`PushoutRightImageDecision.lean` (r4) shipped the TWO-SIDED right-image (single-gap) decider
`pushoutRightImageTwoSidedDecision`.  This file GENERALIZES the forward assembly from the hard-coded THREE gaps to
an ARBITRARY LIST of gaps, and feeds the r4 two-sided decision into that assembly.

## The fixed-wire-count scope (endo gaps) is EXACTLY the honestly-decidable disjoint case

A pushout 2-cell has NO `s`-generator 2-cells (the involution is thin — its `s·s = id` lives at the 1-cell level,
never injected as a pushout 2-cell); the only 2-cell generators are the monad `eta` (`t^0 ⇒ t`) and `mu`
(`t^2 ⇒ t`).  So every pushout 2-cell is monad activity (`eta`, `mu`) whiskered by `s`/`t` contexts and vertically
composed.  When every gap is an ENDOMORPHISM (`t^k ⇒ t^k`, e.g. the left-unit collapse `t ⇒ t` or its normal form
`id_t`), the total wire count is preserved dom-to-cod, so the `s`-walls sit at FIXED absolute positions and the
whole cell is an endomorphism on ONE fixed interleaved boundary `w = gap · s · gap · s · … · gap`.  This is exactly
the case `threeGapSpliceConv` inhabits (endo on `t·s·t·s·t`), and it is the case where the forward assembly is pure,
wall-inert congruence closure at ARBITRARY arity.

`multiGapEndoSplice` is that generalization: a LIST of positioned endo gap-fills (each a `SaturatedConvOver`
between two parallel endo cells on the shared boundary) splices — by the four one-hole congruences + `trans`,
structurally over the list — into ONE boundary convertibility from the source assembly `endoGapFoldSource` to the
canonical `wallGapCanonicalForm` (each gap at its target/NF).  `threeGapSpliceConv`'s construction is the
three-element instance of this fold.

## What the r4 two-sided decision contributes (B2)

`decidedLeftUnitRightImageConv` RUNS `pushoutRightImageTwoSidedDecision` on the reconstructed left-unit pair
(`reconLeftUnitCell` / `reconIdTCell`) and takes its `isTrue` verdict (the `isFalse` branch discharged by the
shipped `pushoutRightImageCompletenessLift reconLeftUnitReflectsTrue`).  Whiskered into the three wall positions it
yields three `EndoGapFill`s, and `multiGapEndoSplice` assembles them into one whole-cell pushout convertibility —
the r4 single-gap two-sided decision fed through the arbitrary-arity forward splice.

## The wall, pinned (the WIRE-CHANGING factorization stays walled)

The FULL arbitrary-word decision needs to FACTOR an ARBITRARY interleaved pushout cell into wall/gap-whiskered
form.  For WIRE-CHANGING cells (a gap `t^a ⇒ t^b`, `a ≠ b`, from a genuine `eta`/`mu` firing) the total wire count
is NOT preserved, so the `s`-walls SHIFT dom-to-cod and the cell is NOT endo — the fixed-boundary splice does not
apply.  Two residuals wall it, neither authorable here:

  * **The purification / convex-block projection (residual (iii), `DispatchSaturated.lean`).**  Every pushout
    derivation must project back to per-component derivations; the monad unit/mult WIRE-CREATING generators break
    the convex-block projection (Nelson-Oppen / Baader-Tinelli is sound only for word-preserving / left-connected
    presentations).  This is exactly the wall-shifting the endo scope excludes.
  * **The gap-flush signature transport (the missing WalkingMonad-lane object).**  Collapsing a wire-changing gap
    to its Eilenberg-Zilber normal form rides the CONSUME-only `WalkingMonad/MonadWordVcomp.wordMul_vcomp`
    (`:473`, valued in the BESPOKE `MonadSaturatedTwoCellConv` over `monadModeSignature`).  Feeding a
    reconstructed-signature completeness lift needs the SIGNATURE-TRANSPORTED image of that fact
    (`wordMul_vcomp` reseated onto `monadComputad.toModeSignature` / `MonadLawRelReconstructed`) — a monad-lane
    object that does NOT yet exist and that the Amalgam lane may only CONSUME, not author.

So `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false`,
`fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`, and #2043 remains OPEN at the
shared-generator / wire-changing scope (WP-AMALG-3 territory).  No fabricated flip.

Raw Lean 4 + Init.  STRUCTURAL on `List`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The fixed-boundary gap-fill and the arbitrary-arity vertical fold -/

/-- A **fixed-boundary gap-fill** — a saturated convertibility between two PARALLEL endomorphism cells on ONE
shared interleaved `boundary` (both `boundary ⇒ boundary`).  This is one gap of a wall/gap-whiskered layout whose
wire count is fixed (so the surrounding `s`-walls do not shift): its `source` is the gap's presented content and
its `target` is that gap's normal form.  A list of these is a whole wall/gap-endo cell. -/
structure EndoGapFill (signature : ModeSignature) (baseRel : CellRel signature)
    {sourceMode targetMode : signature.graph.Mode}
    (boundary : ModalityPath signature.graph sourceMode targetMode) : Type where
  /-- The gap's presented content (an endomorphism on the shared boundary). -/
  source : RawTwoCellExpr signature boundary boundary
  /-- The gap's normal form (an endomorphism on the shared boundary). -/
  target : RawTwoCellExpr signature boundary boundary
  /-- The per-gap convertibility (typically a whiskered right-image collapse). -/
  fill : SaturatedConvOver signature baseRel source target

/-- The **source assembly** of a gap-fill list — the vertical composite of the gaps' presented contents (each an
endomorphism on the shared boundary), the presented wall/gap-endo cell.  Structural on the list; the empty layout
is the identity. -/
def endoGapFoldSource {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {boundary : ModalityPath signature.graph sourceMode targetMode} :
    List (EndoGapFill signature baseRel boundary) → RawTwoCellExpr signature boundary boundary
  | [] => RawTwoCellExpr.id boundary
  | fill :: rest => RawTwoCellExpr.vcomp fill.source (endoGapFoldSource rest)

/-- ★ **The wall/gap canonical form** — the vertical composite of the gaps' NORMAL FORMS (each `target`), the
canonical (all-gaps-normalized) assembly of a fixed-wire-count wall/gap layout.  The forward splice lands the
source assembly here.  (The arbitrary-CELL version — factoring a raw interleaved pushout cell into such a fill list
— is the walled residual for the wire-CHANGING case; see the file docstring.) -/
def wallGapCanonicalForm {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {boundary : ModalityPath signature.graph sourceMode targetMode} :
    List (EndoGapFill signature baseRel boundary) → RawTwoCellExpr signature boundary boundary
  | [] => RawTwoCellExpr.id boundary
  | fill :: rest => RawTwoCellExpr.vcomp fill.target (wallGapCanonicalForm rest)

/-- ★★★ **THE ARBITRARY-ARITY FORWARD SPLICE (fixed wire count).**  A LIST of fixed-boundary gap-fills splices
into ONE boundary convertibility: the source assembly `endoGapFoldSource fills` (the presented wall/gap-endo cell)
is saturated-convertible to `wallGapCanonicalForm fills` (every gap at its normal form).  Structural on the list —
`[]` is `refl` on the identity; `fill :: rest` threads the head gap's convertibility by `vcompCongrLeft` and the
tail's spliced convertibility by `vcompCongrRight`, joined by `trans`.  Pure congruence closure, wall-inert,
hypothesis-FREE, over ANY signature and base relation.  This generalizes `threeGapSpliceConv` (the hard-coded
three-gap, two-`s`-wall word) to an ARBITRARY number of gaps: `threeGapSpliceConv`'s construction is the
three-element instance of this fold. -/
theorem multiGapEndoSplice {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {boundary : ModalityPath signature.graph sourceMode targetMode} :
    (fills : List (EndoGapFill signature baseRel boundary)) →
    SaturatedConvOver signature baseRel (endoGapFoldSource fills) (wallGapCanonicalForm fills)
  | [] => SaturatedConvOver.refl (RawTwoCellExpr.id boundary)
  | fill :: rest =>
      SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft (endoGapFoldSource rest) fill.fill)
        (SaturatedConvOver.vcompCongrRight fill.target (multiGapEndoSplice rest))

/-! ## B1 non-vacuity — the general splice fires on a genuine three-gap, two-`s`-wall layout -/

/-- The three per-gap collapses of the two-`s`-wall word `t·s·t·s·t`, packaged as fixed-boundary gap-fills — each
the shipped base-case collapse `gapCollapse` (the left-unit gap-image `t ⇒ t` made pushout-convertible to the
identity gap-image) whiskered into its wall position.  The three positions share ONE endo boundary
(`t·s·t·s·t`). -/
def multiGapForwardFills :
    List (EndoGapFill involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (boundary := composePath (mapPath multiGapInclRight.toComputadMorphism monadComputadReconstructedT)
        (composePath monadPushSPath (composePath monadPushTPath (composePath monadPushSPath monadPushTPath))))) :=
  [ { source := gapPositionOne gapLeftUnitImage, target := gapPositionOne gapIdImage,
      fill := SaturatedConvOver.whiskerRightCongr
        (composePath monadPushSPath (composePath monadPushTPath (composePath monadPushSPath monadPushTPath)))
        gapCollapse },
    { source := gapPositionTwo gapLeftUnitImage, target := gapPositionTwo gapIdImage,
      fill := SaturatedConvOver.whiskerLeftCongr (composePath monadPushTPath monadPushSPath)
        (SaturatedConvOver.whiskerRightCongr (composePath monadPushSPath monadPushTPath) gapCollapse) },
    { source := gapPositionThree gapLeftUnitImage, target := gapPositionThree gapIdImage,
      fill := SaturatedConvOver.whiskerLeftCongr
        (composePath monadPushTPath (composePath monadPushSPath (composePath monadPushTPath monadPushSPath)))
        gapCollapse } ]

/-- ★★ **The general splice fires on the three-gap layout.**  `multiGapEndoSplice` applied to the three positioned
left-unit collapses produces a single pushout convertibility from the presented three-gap assembly to its
canonical (all-gaps-`id_t`) form — the arbitrary-arity forward splice, non-vacuous on the same genuine two-`s`-wall,
three-`t`-gap word `threeGapSpliceConv` (r4) inhabited by a bespoke three-fold construction. -/
def multiGapForwardSpliceWitness :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (endoGapFoldSource multiGapForwardFills) (wallGapCanonicalForm multiGapForwardFills) :=
  multiGapEndoSplice multiGapForwardFills

/-! ## B2 — the r4 two-sided decision fed through the arbitrary-arity splice -/

/-- ★★ **The left-unit gap-image convertibility, EXTRACTED FROM THE r4 TWO-SIDED DECIDER.**  Runs
`pushoutRightImageTwoSidedDecision` on the reconstructed left-unit pair and takes its `isTrue` verdict; the
`isFalse` branch is discharged by the shipped B2-forward lift on `reconLeftUnitReflectsTrue`.  This is the genuine
decider-routed per-gap collapse (as opposed to `gapCollapse`, which uses the lift directly). -/
def decidedLeftUnitRightImageConv :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      gapLeftUnitImage gapIdImage :=
  match pushoutRightImageTwoSidedDecision reconLeftUnitCell reconIdTCell with
  | isTrue conv => conv
  | isFalse hno => absurd (pushoutRightImageCompletenessLift reconLeftUnitReflectsTrue) hno

/-- The three wall-positioned gap-fills whose per-gap convertibility is the DECIDER-EXTRACTED
`decidedLeftUnitRightImageConv` (not the direct lift `gapCollapse`).  Same two-`s`-wall layout as
`multiGapForwardFills`, now routed through the r4 two-sided decision. -/
def decidedMultiGapFills :
    List (EndoGapFill involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (boundary := composePath (mapPath multiGapInclRight.toComputadMorphism monadComputadReconstructedT)
        (composePath monadPushSPath (composePath monadPushTPath (composePath monadPushSPath monadPushTPath))))) :=
  [ { source := gapPositionOne gapLeftUnitImage, target := gapPositionOne gapIdImage,
      fill := SaturatedConvOver.whiskerRightCongr
        (composePath monadPushSPath (composePath monadPushTPath (composePath monadPushSPath monadPushTPath)))
        decidedLeftUnitRightImageConv },
    { source := gapPositionTwo gapLeftUnitImage, target := gapPositionTwo gapIdImage,
      fill := SaturatedConvOver.whiskerLeftCongr (composePath monadPushTPath monadPushSPath)
        (SaturatedConvOver.whiskerRightCongr (composePath monadPushSPath monadPushTPath)
          decidedLeftUnitRightImageConv) },
    { source := gapPositionThree gapLeftUnitImage, target := gapPositionThree gapIdImage,
      fill := SaturatedConvOver.whiskerLeftCongr
        (composePath monadPushTPath (composePath monadPushSPath (composePath monadPushTPath monadPushSPath)))
        decidedLeftUnitRightImageConv } ]

/-- ★★★ **THE r4 TWO-SIDED DECISION, ASSEMBLED ACROSS THREE GAPS.**  The r4 single-gap two-sided decider's `isTrue`
verdict (extracted per gap by `decidedLeftUnitRightImageConv`), whiskered into the two-`s`-wall layout, is spliced
by the arbitrary-arity `multiGapEndoSplice` into ONE whole-cell pushout convertibility from the presented three-gap
assembly to its canonical form.  This is the honest ASSEMBLY the round targets: the r4 two-sided (single-gap)
decision fed through the fixed-wire-count forward splice.  The full ARBITRARY-word (wire-CHANGING) decision stays
walled — see the file docstring. -/
def decidedMultiGapSpliceWitness :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (endoGapFoldSource decidedMultiGapFills) (wallGapCanonicalForm decidedMultiGapFills) :=
  multiGapEndoSplice decidedMultiGapFills

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the ARBITRARY-ARITY forward splice (fixed wire count) SHIPS.**  `= true`:
`multiGapEndoSplice` splices an ARBITRARY LIST of fixed-boundary gap-fills into one boundary convertibility
(`endoGapFoldSource fills ≈ wallGapCanonicalForm fills`), structurally over the list by the shipped
`SaturatedConvOver` congruences — generalizing the hard-coded three-gap `threeGapSpliceConv` (r4) to any number of
gaps, over any signature and base relation.  Non-vacuous on the genuine two-`s`-wall, three-`t`-gap word
(`multiGapForwardSpliceWitness`).  And the r4 TWO-SIDED single-gap decision feeds it: its `isTrue` verdict
(`decidedLeftUnitRightImageConv`, extracted from `pushoutRightImageTwoSidedDecision`) whiskered across the three
walls assembles into one whole-cell pushout convertibility (`decidedMultiGapSpliceWitness`).  `= true`. -/
def fxAmalg_hasMultiGapEndoSpliceGeneral : Bool := true

/-- **Honesty marker — the WIRE-CHANGING (non-endo) factorization STAYS WALLED; #2043 does NOT close.**  `= true`
(the wall is honestly held).  The fixed-wire-count forward splice ships at arbitrary arity, and the r4 two-sided
decision feeds it.  The FULL arbitrary-word decision needs to FACTOR an arbitrary interleaved pushout cell into
wall/gap-whiskered form; for WIRE-CHANGING cells (a gap `t^a ⇒ t^b`, `a ≠ b`, from a genuine `eta`/`mu` firing) the
wire count is not preserved, the `s`-walls SHIFT, and the cell is NOT endo — the fixed-boundary splice does not
apply.  Two residuals wall it: (i) the purification / convex-block projection (residual (iii),
`DispatchSaturated.lean` — the wire-creating generators break the projection), and (ii) the gap-flush signature
transport (the reconstructed-signature reseat of the CONSUME-only `WalkingMonad/MonadWordVcomp.wordMul_vcomp`, a
monad-lane object that does NOT yet exist).  So `fxAmalg_hasFullSaturatedPushoutDispatch`
(`DispatchSaturated.lean`) STAYS `false`, `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`,
and #2043 remains OPEN at the wire-changing / shared-generator scope (WP-AMALG-3).  No fabricated flip.  `= true`. -/
def fxAmalg_arbitraryCellFactorizationStaysWalled : Bool := true

end FX1Poly.Polygraph.Amalgam
