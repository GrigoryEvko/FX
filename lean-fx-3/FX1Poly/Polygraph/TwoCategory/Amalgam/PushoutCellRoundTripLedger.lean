import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeCellInvertRoundTrip
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestPayloadZip
import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchSaturated
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutBundle
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompInterchangeSplice

/-! # Polygraph/TwoCategory/Amalgam/PushoutCellRoundTripLedger — the r13 LEDGER: the BACKWARD cell round-trip + the
payload-zip aligned target ship; the MASTER RE-AUDIT against the three verbatim demands; the three masters HOLD;
#2043 stays OPEN (WP-AMALG-2 r13, the backward round-trip + payload zip round)

The r12 ledger (`PushoutCellConverseLedger.lean`) shipped the FORWARD cell converse `wallFreeCellInvert` + its
gen-case backward SECTION and named TWO follow-on nodes: (1) the FULL cell backward round-trip (a
`reseatCellInv_reseatCell`-style fuel assembly) and (2) the payload-carrying finest common-refinement zip.  r13
closes node (1) in full and ships the aligned TARGET of node (2), re-auditing the three masters against their
VERBATIM demands.  This file records the r13 section of the ledger.  It flips NOTHING.

## What r13 SHIPPED (machine-checked, zero-axiom)

  * **The FULL cell backward round-trip** (`PushoutWallFreeCellInvertRoundTrip.lean`) —
    `mapCellAlong inclRight (wallFreeCellInvert cell wfS wfT) = castBoundary (mapPath_inclRight_pathInvert ..) cell`
    (`mapCellAlong_inclRight_wallFreeCellInvert`), all five `RawTwoCellExpr` constructors, the exact mirror of the
    shipped `reseatCellInv_reseatCell`: the two cast-fusion whisker step theorems
    (`mapCellAlongWallFreeInvertWhiskerLeftStep` / `..RightStep`), the gen-case FULL round-trip
    (`wallFreeGenInvert_onTwoCell_full`, upgrading the r12 index round-trip via `Subtype.ext`), and the structural
    cell-size fuel (`mapCellAlongWallFreeInvertFueled`, the free middle mode pinned by `pushoutModeUnique`).  The
    PATH leg is FREE (`mapPath_inclRight_pathInvert` is word-routed) — strictly cheaper than the reseat precedent.
    TRUTH-PROBED on the r12 whiskered probes + fresh `vcomp` / `gen` cells.  Paired with the r11 1-cell bijection
    into `pushoutCellRoundTripBijection` (dim-1 boundary + dim-2 interior).

  * **The payload-zip aligned TARGET** (`PushoutFinestPayloadZip.lean`) — `pushoutFactorizeVcompSeamFinest`: the r9
    vcomp seam INSTANTIATED at the finest common refinement (`finalWall = nil`, `pairs = finestLayout G`), legalized
    by the r12 all-boundary round-trips (`finestLayoutPresentsAllBoundaries`).  The r8 shape's SKELETON aligns to the
    finest keys (`finestLayoutAlignsR8Shape`), and the seam-at-finest FIRES end-to-end
    (`pushoutFactorizeVcompSeamFinestReflProbe`).

## The MASTER RE-AUDIT — each of the three verbatim demands re-checked against the r13 inventory

### Master (i) `fxAmalg_hasFullSaturatedPushoutDispatch = false` (`DispatchSaturated.lean`)

VERBATIM three walls: "(i) a genuine-generator coprojection `onTwoCell` needs `interpretWordFrom_map`; (ii) the only
shipped real saturated decider … lives over the BESPOKE `monadModeSignature`, not the RECONSTRUCTED
`monadComputad.toModeSignature`, so it needs the reconstruction-faithfulness iso; (iii) COMPLETENESS — every pushout
derivation must project back to per-component derivations (Nelson-Oppen / Baader-Tinelli purification, sound only for
word-preserving / left-connected component presentations; the unit/counit wire-creating generators break the convex-
block projection)."

Re-audit: walls (i) and (ii) are now STALE — (i) is closed (`fxAmalg_hasRealGeneratorCoprojection = true`,
`RealCoprojection.lean`'s `inclusionRightTwoReal`), (ii) is closed (`monadReconstructedDecision`, the UNCONDITIONAL
decider over the reconstructed signature, `ReconstructedDecision.lean`).  The r13 backward cell round-trip delivers
the essential-surjectivity CONVERSE (monad-cells ↔ wall-free pushout-cells at the single mode, a section).  But the
BLOCKING conjunct is (iii) COMPLETENESS — a cross-lane / wire-creating-regime structural wall the CONVERSE does NOT
address (essential-surjectivity is not purification-completeness).  Nothing r13 built meets (iii) LITERALLY.  STAYS
`false`.

### Master (ii) `fxAmalg_hasGeneralPushoutDispatch = false` (`PushoutBundle.lean`)

VERBATIM: "the GENERAL decision procedure: a `Decidable (SaturatedConvOver involutionMonadPushout.toModeSignature …)`
for ARBITRARY pushout pairs.  That needs either (i) the reconstruction decider reseat (fib-3-coupled) or (ii) the
purification-reflection completeness … The arity-fold gives an unconditional isFalse on any pair whose monotone maps
differ, and an isTrue on any free/whisker-exchange pair — a partial-but-sound decision, not the full dispatch."

Re-audit: the r13 backward round-trip + payload zip give MORE partial-but-sound coverage (the arity-fold isFalse +
the free/whisker isTrue + the converse), but NOT the full arbitrary-pair `Decidable`.  Neither branch (i) fib-3-coupled
reseat nor (ii) purification completeness is met LITERALLY.  STAYS `false`.

### Master (iii) `fxAmalg_topFactorizationInductionStaysWalled = true` (`PushoutVcompInterchangeSplice.lean`)

VERBATIM: "That top induction additionally needs: (a) the `blockDecompose`↔`composePath` reconstruction bridge to READ
a canonical `VcompGapPair` list off an arbitrary cell's boundary; (b) the per-case assembly …; (c) the decider wiring."

Re-audit: the payload zip's re-slice is precisely ingredient (b) for the vcomp case — and it is the part that does NOT
close (the atomic-firing obstruction: `finestLayout` refines the SKELETON but not the atomic PAYLOADS; the correct
common refinement is a FIRING-BLOCK decomposition, the named residual).  The r13 backward `wallFreeCellInvert`
round-trip delivers the per-gap reconstruction-inversion the r9 seam flagged (recognize a pure-`t` gap as
`mapCellAlong inclRight (monadCell)`, the converse of `interpretWordFrom_map`), but the whisker-frame `t`-run merge
AND the payload re-slice remain.  Nothing r13 built discharges (a)/(b)/(c) LITERALLY.  STAYS `true` (walled).

### Finding-C — the honest cross-lane HOLD

Finding-C (the multi-gap NORMAL-FORM splice) is STILL CROSS-LANE BLOCKED on `WalkingMonad.wordMul_vcomp` (CONSUME-only,
the `WalkingMonad/` READ-ONLY lane); untouched.  This is the honest hold: the factorize-decide assembly over the new
r13 inventory cannot complete while Finding-C's normal-form splice is blocked cross-lane.

## HELD — the three masters do NOT flip (the honest r13 verdict)

Per their VERBATIM demands, NONE is literally met by the backward round-trip or the payload-zip target:

  * `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false` — blocked on (iii) completeness.
  * `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false` — no full arbitrary-pair decider.
  * `fxAmalg_topFactorizationInductionStaysWalled` (`PushoutVcompInterchangeSplice.lean`) STAYS `true` — ingredient
    (b) (the payload re-slice) does not close.

**#2043 does NOT close.**  This file adds markers ONLY; it touches no shipped marker.  No fabricated flip.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The shipped r13 nodes, machine-witnessed -/

-- The FULL cell backward round-trip + its two cast-fusion step theorems + the gen full round-trip.
#check @mapCellAlong_inclRight_wallFreeCellInvert
#check @mapCellAlongWallFreeInvertWhiskerLeftStep
#check @mapCellAlongWallFreeInvertWhiskerRightStep
#check @wallFreeGenInvert_onTwoCell_full
-- The dim-2 bijection paired with the r11 dim-1 one.
#check @pushoutCellRoundTripBijection
-- The payload-zip aligned target + the r8 skeleton alignment.
#check @pushoutFactorizeVcompSeamFinest
#check @finestLayoutAlignsR8Shape
-- The three masters STAY put (referenced, not touched).
#check @fxAmalg_hasFullSaturatedPushoutDispatch
#check @fxAmalg_hasGeneralPushoutDispatch
#check @fxAmalg_topFactorizationInductionStaysWalled

/-! ## Honesty markers — the r13 ledger -/

/-- ★★★ **Honesty marker — the BACKWARD cell round-trip + the payload-zip aligned target SHIP; #2043 stays OPEN.**
`= true` (the honest r13 verdict).  r12 shipped the FORWARD cell converse + the gen backward SECTION and named two
follow-on nodes; r13 closed node (1) — the FULL cell backward round-trip `mapCellAlong inclRight ∘ wallFreeCellInvert
= castBoundary .. cell` (all five constructors, the exact mirror of `reseatCellInv_reseatCell`, PATH leg FREE) — and
shipped the aligned TARGET of node (2) — the vcomp seam at the finest common refinement
(`pushoutFactorizeVcompSeamFinest`), with the r8 skeleton alignment self-attack.  Both zero-axiom, truth-probed.
FLIPPED NO master: `fxAmalg_hasFullSaturatedPushoutDispatch` STAYS `false`, `fxAmalg_hasGeneralPushoutDispatch` STAYS
`false`, `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close — no fabricated flip.
`= true`. -/
def fxAmalg_r13BackwardRoundTripAndZipShip : Bool := true

/-- ★★ **Honesty marker — the MASTER RE-AUDIT against the three VERBATIM demands, flipping ONLY what is LITERALLY met
(nothing).**  `= true` (the wall honestly held, each demand re-checked against the r13 inventory).  Master (i)
`fxAmalg_hasFullSaturatedPushoutDispatch`: walls (i)/(ii) are STALE (closed by `RealCoprojection` /
`ReconstructedDecision`); the blocking conjunct is (iii) COMPLETENESS (Nelson-Oppen / Baader-Tinelli purification for
the wire-creating regime) — the backward round-trip is the essential-surjectivity CONVERSE, NOT completeness; STAYS
`false`.  Master (ii) `fxAmalg_hasGeneralPushoutDispatch`: the round-trip + zip give MORE partial-but-sound coverage,
NOT the full arbitrary-pair `Decidable` (neither fib-3-coupled reseat nor purification completeness); STAYS `false`.
Master (iii) `fxAmalg_topFactorizationInductionStaysWalled`: the payload zip's re-slice is ingredient (b) of the top
induction and does NOT close (the atomic-firing obstruction — `finestLayout` refines the skeleton, not the payloads;
the firing-block decomposition is the residual); the backward round-trip delivers the per-gap reconstruction-inversion,
but the whisker-frame merge + payload re-slice remain; STAYS `true`.  No demand is met LITERALLY; no marker flips.
`= true`. -/
def fxAmalg_r13MasterReauditHolds : Bool := true

/-- ★★ **Honesty marker — the #2043 STATE: what remains to the close, each jam a NAMED node.**  `= true`.  #2043
(the FULL saturated pushout dispatch / general dispatch / top factorization) remains OPEN after r13.  What remains:

  * **The purification/projection COMPLETENESS (master i, residual iii)** — every pushout derivation projects back to
    per-component derivations; the wire-creating unit/counit generators break the convex-block projection.  A cross-lane
    / regime-structural wall the essential-surjectivity converse does NOT touch.  Named node: the Nelson-Oppen /
    Baader-Tinelli / Ghilardi-Nicolini-Zucchelli purification-reflection for the wire-creating regime.

  * **The firing-block payload re-slice (master iii, ingredient b)** — re-express two arbitrary payload-bearing
    factorizations against a firing-block decomposition (gap-slot per maximal firing region), consuming
    `finestGapWidthsAux_append` at the CELL level to fuse adjacent firing regions across a `composePath` junction cast.
    Named node: `mergeFrameIntoHead` / `mergeFrameIntoTail`, the cell-level surgery + the whisker-frame `t`-run merge.

  * **The factorize-decide ASSEMBLY over the new inventory (master ii)** — wire the backward round-trip + the seam-at-
    finest + the per-gap reconstruction-inversion into a total `Decidable (SaturatedConvOver …)`.  This assembly
    CANNOT complete while Finding-C's multi-gap NORMAL-FORM splice is CROSS-LANE BLOCKED on
    `WalkingMonad.wordMul_vcomp` (the `WalkingMonad/` READ-ONLY lane, CONSUME-only) — the honest hold.

Every jam is an exact goal with a named node.  r13 adds markers ONLY; the three masters and the arbitrary-cell decision
stay put; nothing in the `WalkingMonad/` READ-ONLY lane was edited.  No fabricated flip.  `= true`. -/
def fxAmalg_r13StateLedger : Bool := true

end FX1Poly.Polygraph.Amalgam
