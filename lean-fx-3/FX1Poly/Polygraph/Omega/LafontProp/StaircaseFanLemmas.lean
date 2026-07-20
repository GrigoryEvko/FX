import FX1Poly.Polygraph.Omega.LafontProp.StaircaseAssembly

/-! # Polygraph/Omega/LafontProp/StaircaseFanLemmas — the staircase-fan supersession

This file closes the LAFONT-REPAIR staircase-fan round by SUPERSEDING six committed
owner-false markers with fresh true markers, and by re-firing each of the four fan cores at
NEW small instances disjoint from the committed fires.

## What this round found (strata drift: code ahead of the markers)

The commission listed six live owner-false markers as open targets:

* `lstMuFanDuplicationProved := false`            (StaircaseCompleteness)
* `lstDeltaFanFusionProved := false`              (StaircaseCompleteness)
* `lstCrossingTwoFanSwapProved := false`          (StaircaseCompleteness)
* `lstCanonicalReductionOverStrictLayersProved := false` (StaircaseCompleteness)
* `lcoCrossingTwoFanSwapProved := false`          (StaircaseCores)
* `fxLafontStrictLayer_hasCanonicalCompleteness := false` (StrictLayerEmbedding)

Every one of the four named Props those markers bill is ALREADY INHABITED, zero-axiom, in
committed sibling files, and the whole chain builds green:

* `lstMuFanDuplicationStatement`   — `lcoMuFanDuplicationHolds`   (StaircaseCores)
* `lstDeltaFanFusionStatement`     — `lcoDeltaFanFusionHolds`     (StaircaseCores)
* `lstCrossingTwoFanSwapStatement` — `lcxCrossingTwoFanSwapHolds` (StaircaseCrossingCore,
  the crossing core's second attack — the conjugation route — landed the two-fan swap that
  the burned first attack could not align)
* `lstCanonicalReductionOverStrictLayersStatement` — `lsaCanonicalReductionHolds`
  (StaircaseAssembly), with `fxLafontStaircase_canonicalCompletenessProven := true`.

Independent `#print axioms` on all four confirms `does not depend on any axioms`.  The frozen
owner Bools stay byte-intact false as history; this file records their supersession with new
true markers and a fresh, non-vacuous fire suite.

## The fires (relation-diff gate honoured, fan denotes never forced to reduce)

Each fan-level Conv fire is instantiated at a fresh column set and consumed through the
abstract soundness bridge `sldConvertibleLayersDenoteAgreeUpTo` (which proves
`doEntriesAgreeUpTo = true` WITHOUT reducing the expensive ladder denotation).  The
relation-diff SEMANTIC pins ride the cheap scale-tower / 1x1 denotations that the fans are
built from — kernel `rfl`, matching the committed `lcoScaleMuMatrixPin` /
`lcoScaleFusionMatrixPin` / `lcoDistinctScaleTowersStayApart` cost class:

* MU (col 3): `mu ; scale(3)` denotes the duplicated row `[3, 3]` — the fan's duplication.
* DELTA (cols 3, 4): the fused tower `scale(7)` denotes `[7] = 3 + 4` — the fan's fusion.
* CROSSING (cols 2, 5): the two swapped scalar contents `scale(2)` / `scale(5)` are distinct
  and stay non-convertible — the swap exchanges GENUINELY different fans.
* CANONICAL REDUCTION (closed loop `epsilon ; eta`): denotes the zero 1x1 matrix, distinct
  from the bare wire, and stays non-convertible — a fresh diagram beyond the committed
  doubling / crossing / identity fires.

Raw Lean 4 + Init only; zero-axiom; audit twin with per-decl `#assert_no_axioms` plus an
independent `#print axioms` probe. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.LafontProp

/-! ## Fresh ascriptions of the four fan-core statements against the live Props -/

/-- The mu fan-duplication statement, inhabited from this module via the committed core. -/
theorem lsfMuFanDuplicationHolds : lstMuFanDuplicationStatement :=
  lcoMuFanDuplicationHolds

/-- The delta fan-fusion statement, inhabited from this module via the committed core. -/
theorem lsfDeltaFanFusionHolds : lstDeltaFanFusionStatement :=
  lcoDeltaFanFusionHolds

/-- The crossing two-fan-swap statement, inhabited from this module via the committed core
(the conjugation-route attack in `StaircaseCrossingCore`). -/
theorem lsfCrossingTwoFanSwapHolds : lstCrossingTwoFanSwapStatement :=
  lcxCrossingTwoFanSwapHolds

/-- The full canonical reduction over strict layers, inhabited from this module via the
committed assembly. -/
theorem lsfCanonicalReductionHolds : lstCanonicalReductionOverStrictLayersStatement :=
  lsaCanonicalReductionHolds

/-! ## T1 — mu fan duplication, fresh fire at column 3 -/

/-- MU FAN-DUPLICATION FIRE (t = 1, constant column 3): the duplicated-fan conversion at a
column disjoint from the committed core fire (which used column 2). -/
theorem lsfMuFanDuplicationFire :
    SldAreConvertibleLayers 3
      (sldAppendCells (sldWireLayerOfArity 1) [SldCell.generatorMu]
        :: lstFanLayerList 1 (fun _sourceRow => 3))
      (sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 3)))
        (lstFanLayerList 1 (fun _sourceRow => 3))) :=
  lsfMuFanDuplicationHolds 1 (fun _sourceRow => 3)

/-- MU FIRE consumed through soundness: both sides denote the same matrix on the 1x3
rectangle — `acc + 3 * (x + y) = (acc + 3 * x) + 3 * y`. -/
theorem lsfMuFanDuplicationFireDenotesEqually :
    doEntriesAgreeUpTo 1 3
      (sldLayersDenote
        (sldAppendCells (sldWireLayerOfArity 1) [SldCell.generatorMu]
          :: lstFanLayerList 1 (fun _sourceRow => 3)))
      (sldLayersDenote
        (sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 3)))
          (lstFanLayerList 1 (fun _sourceRow => 3)))) = true :=
  sldConvertibleLayersDenoteAgreeUpTo lsfMuFanDuplicationFire 1

/-- MU RELATION-DIFF PIN (kernel `rfl`): the duplicated scale tower denotes the row
`[3, 3]` — both summands enter with scale 3, the semantic content the fan duplicates. -/
theorem lsfMuDuplicatesScaleMatrixPin :
    (Nat.beq (sldLayersDenote ([SldCell.generatorMu] :: lstScaleLayerList 3) 0 0) 3
      && Nat.beq (sldLayersDenote ([SldCell.generatorMu] :: lstScaleLayerList 3) 0 1) 3)
      = true := rfl

/-! ## T2 — delta fan fusion, fresh fire at columns 3 and 4 -/

/-- DELTA FAN-FUSION FIRE (t = 1, columns 3 and 4): the fused-fan conversion at a column pair
disjoint from the committed core fire (which used columns 1 and 2). -/
theorem lsfDeltaFanFusionFire :
    SldAreConvertibleLayers 2
      (sldAppendCells (sldWireLayerOfArity 1) [SldCell.generatorDelta]
        :: sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 3)))
            (lstFanLayerList 1 (fun _sourceRow => 4)))
      (lstFanLayerList 1 (fun mergeRow => (fun _sourceRow => 3) mergeRow
        + (fun _sourceRow => 4) mergeRow)) :=
  lsfDeltaFanFusionHolds 1 (fun _sourceRow => 3) (fun _sourceRow => 4)

/-- DELTA FIRE consumed through soundness: both sides denote the same matrix on the 1x2
rectangle — `(acc + 3 * x) + 4 * x = acc + 7 * x`. -/
theorem lsfDeltaFanFusionFireDenotesEqually :
    doEntriesAgreeUpTo 1 2
      (sldLayersDenote
        (sldAppendCells (sldWireLayerOfArity 1) [SldCell.generatorDelta]
          :: sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 3)))
              (lstFanLayerList 1 (fun _sourceRow => 4))))
      (sldLayersDenote (lstFanLayerList 1 (fun _sourceRow => 7))) = true :=
  sldConvertibleLayersDenoteAgreeUpTo lsfDeltaFanFusionFire 1

/-- DELTA RELATION-DIFF PIN (kernel `rfl`): the fused tower denotes `[7]` — `3 + 4 = 7` at
the matrix level, the semantic content the two fans fuse into. -/
theorem lsfDeltaFusesScaleMatrixPin :
    Nat.beq (sldLayersDenote (lstScaleLayerList 7) 0 0) 7 = true := rfl

/-! ## T3 — crossing two-fan swap, fresh fire at columns 2 and 5 -/

/-- CROSSING TWO-FAN-SWAP FIRE (t = 1, columns 2 and 5): the swap conversion at a column pair
disjoint from the committed core fire (which used columns 1 and 2). -/
theorem lsfCrossingTwoFanSwapFire :
    SldAreConvertibleLayers 3
      (sldAppendCells (sldWireLayerOfArity 1) [SldCell.crossing]
        :: sldAppendLayers
            (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 2)))
            (lstFanLayerList 1 (fun _sourceRow => 5)))
      (sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 5)))
        (lstFanLayerList 1 (fun _sourceRow => 2))) :=
  lsfCrossingTwoFanSwapHolds 1 (fun _sourceRow => 2) (fun _sourceRow => 5)

/-- CROSSING FIRE consumed through soundness: both sides denote the same matrix on the 1x3
rectangle — `acc + 2 * y + 5 * x = acc + 5 * x + 2 * y` (addition commutes). -/
theorem lsfCrossingTwoFanSwapFireDenotesEqually :
    doEntriesAgreeUpTo 1 3
      (sldLayersDenote
        (sldAppendCells (sldWireLayerOfArity 1) [SldCell.crossing]
          :: sldAppendLayers
              (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 2)))
              (lstFanLayerList 1 (fun _sourceRow => 5))))
      (sldLayersDenote
        (sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 5)))
          (lstFanLayerList 1 (fun _sourceRow => 2)))) = true :=
  sldConvertibleLayersDenoteAgreeUpTo lsfCrossingTwoFanSwapFire 1

/-- CROSSING RELATION-DIFF PIN (kernel `rfl`): the two scalar contents the crossing exchanges
are `scale(2)` and `scale(5)`, denoting `[2]` and `[5]` — genuinely different fans. -/
theorem lsfCrossingSwapsDistinctScalesPin :
    (Nat.beq (sldLayersDenote (lstScaleLayerList 2) 0 0) 2
      && Nat.beq (sldLayersDenote (lstScaleLayerList 5) 0 0) 5) = true := rfl

/-- CROSSING NON-VACUITY (refutation-style span distinctness): the two scale towers the
crossing swaps stay NON-convertible — the swap machinery did not collapse `scale(2)` onto
`scale(5)`. -/
theorem lsfDistinctScaleTowersStayApart :
    SldAreConvertibleLayers 1 (lstScaleLayerList 2) (lstScaleLayerList 5) -> False :=
  sldNotConvertibleOfDistinctDenotes (lstScaleLayerList 2) (lstScaleLayerList 5) 1 rfl

/-! ## T4 — canonical reduction over strict layers, fresh fire on the closed loop -/

/-- CANONICAL-REDUCTION FIRE on the closed loop `epsilon ; eta` (discard then fresh zero):
reduces end-to-end to the canonical form of its own denotation.  Disjoint from the committed
assembly fires (doubling / crossing / identity). -/
theorem lsfCanonicalReductionFireOnClosedLoop :
    SldAreConvertibleLayers 1 [[SldCell.generatorEpsilon], [SldCell.generatorEta]]
      (lstCanonicalLayerList 1 1
        (sldLayersDenote [[SldCell.generatorEpsilon], [SldCell.generatorEta]])) :=
  lsfCanonicalReductionHolds
    { sourceArity := 1, layers := [[SldCell.generatorEpsilon], [SldCell.generatorEta]] } rfl

/-- CLOSED-LOOP FIRE consumed through soundness: both sides denote the same 1x1 matrix. -/
theorem lsfClosedLoopFireDenotesEqually :
    doEntriesAgreeUpTo 1 1
      (sldLayersDenote [[SldCell.generatorEpsilon], [SldCell.generatorEta]])
      (sldLayersDenote
        (lstCanonicalLayerList 1 1
          (sldLayersDenote [[SldCell.generatorEpsilon], [SldCell.generatorEta]]))) = true :=
  sldConvertibleLayersDenoteAgreeUpTo lsfCanonicalReductionFireOnClosedLoop 1

/-- CLOSED-LOOP RELATION-DIFF PIN (kernel `rfl`): the closed loop denotes the ZERO 1x1
matrix — the source is discarded, the output is a fresh zero, independent of the input. -/
theorem lsfClosedLoopMatrixPin :
    Nat.beq (sldLayersDenote [[SldCell.generatorEpsilon], [SldCell.generatorEta]] 0 0) 0
      = true := rfl

/-- CLOSED-LOOP vs WIRE distinctness (kernel `rfl`): the closed loop (zero) and the bare wire
(identity) differ on the 1x1 rectangle. -/
theorem lsfClosedLoopVsWirePin :
    doEntriesAgreeUpTo 1 1
      (sldLayersDenote [[SldCell.generatorEpsilon], [SldCell.generatorEta]])
      (sldLayersDenote [[SldCell.wire]]) = false := rfl

/-- CLOSED-LOOP NON-VACUITY (refutation-style span distinctness): the closed loop and the
bare wire stay NON-convertible — the completeness machinery did not collapse the zero map
onto the identity. -/
theorem lsfClosedLoopVsWireStaysApart :
    SldAreConvertibleLayers 1 [[SldCell.generatorEpsilon], [SldCell.generatorEta]]
      [[SldCell.wire]] -> False :=
  sldNotConvertibleOfDistinctDenotes [[SldCell.generatorEpsilon], [SldCell.generatorEta]]
    [[SldCell.wire]] 1 lsfClosedLoopVsWirePin

/-! ## The new true markers — supersessions of the frozen owner-false Bools

Each committed owner-false Bool stays byte-intact in its file as history; the true markers
below record that the Prop it bills is inhabited zero-axiom (verified in the audit twin). -/

/-- Supersedes `lstMuFanDuplicationProved := false` (StaircaseCompleteness): the mu
fan-duplication core is PROVEN (`lcoMuFanDuplicationHolds`, re-ascribed here). -/
def lsfHasMuFanDuplication : Bool := true

/-- Supersedes `lstDeltaFanFusionProved := false` (StaircaseCompleteness): the delta
fan-fusion core is PROVEN (`lcoDeltaFanFusionHolds`, re-ascribed here). -/
def lsfHasDeltaFanFusion : Bool := true

/-- Supersedes `lstCrossingTwoFanSwapProved := false` (StaircaseCompleteness) and
`lcoCrossingTwoFanSwapProved := false` (StaircaseCores): the crossing two-fan-swap core is
PROVEN (`lcxCrossingTwoFanSwapHolds`, the conjugation route, re-ascribed here). -/
def lsfHasCrossingTwoFanSwap : Bool := true

/-- Supersedes `lstCanonicalReductionOverStrictLayersProved := false` (StaircaseCompleteness)
and `fxLafontStrictLayer_hasCanonicalCompleteness := false` (StrictLayerEmbedding): the full
canonical reduction over strict layers is PROVEN (`lsaCanonicalReductionHolds`, re-ascribed
here); all three fan cores plus the assembly land the Lafont staircase completeness. -/
def lsfHasCanonicalReductionOverStrictLayers : Bool := true

end FX1Poly.Polygraph.Omega.LafontProp
