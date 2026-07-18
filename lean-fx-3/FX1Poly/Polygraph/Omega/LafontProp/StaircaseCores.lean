import FX1Poly.Polygraph.Omega.LafontProp.StaircaseCompleteness

/-! # Polygraph/Omega/LafontProp/StaircaseCores — the mu and delta bottom cores
(LAFONT-REPAIR stage 2 phase 3: TWO OF THE THREE OPEN FAN INTERACTIONS CLOSED)

The staircase file (`StaircaseCompleteness`) closed the wire/eta/epsilon third of the
absorption ladder and left three bottom cores as named owner-false Props.  This file CLOSES
TWO of them — the mu fan duplication and the delta fan fusion — as zero-axiom conversion
derivations over the strict-layer congruence, and records the honest state of the third.

## The derivation ladder (each level rides the one below)

* CROSSING-PAIR KIT: S1 instances at the concrete pads, plus the four MIRRORED naturality
  rows the row table does not carry directly (`lcoCopySlidesBelowParkedStrand` = mirror
  Ndelta, `lcoAddSlidesBelowParkedStrand` = mirror Nmu, `lcoDiscardClimbsAcrossParkedStrand`
  = mirror Neps, `lcoZeroSlidesBelowParkedStrand` = mirror Neta) — each derived by
  sandwiching the direct row between involution pairs.
* PAD-WINDOW ALGEBRA: window-over-pad composition equations and the TWO-SIDED pad
  congruence `lcoConvPadsWindow` (below pad then above pad, refolded).
* SCALE-TAU (`lcoScaleTowerCrossesDown` + mirror `lcoSwapDescendsIntoScaleTower`): the
  crossing is natural against a whole scale tower — the tower-level induction the crossing
  rows only state cell-locally.  Needed by BOTH cores: the bimonoid square emits a crossing.
* SCALE-MU (`lcoScaleTowerDistributesOverAdd`): `mu ; scale(s) ~ (scale(s) | scale(s)) ; mu`
  — B1 opens the square, the copies split, the IH distributes the shorter tower, and the
  emitted crossing dies against the four-strand add tree (`lcoMidSwapDiesAgainstAddTree`,
  M4 at the padded middle add after leaning the tree).
* SCALE-FUSION (`lcoScaleTowersFuseOverCopy`): `delta ; (scale(a) | scale(b)) ; mu ~
  scale(a + b)` — C2 + M2 at zero, coassociativity peel + the mirrored tower crossing +
  one commutativity fire at successor.
* GADGET-MU (`lcoGadgetDistributesOverAdd`): `(wire | mu) ; gadget(s) ~ (gadget(s) | wire) ;
  (wire | gadget(s)) ; (mu | wire)` — left spine (B1 + padded SCALE-MU), right spine (the
  two gadget copies unfolded and slid), met by the FIVE-STRAND MERGE-ROUTE ALIGNMENT
  (`lcoFiveStrandMergeRoutesAgree`: Nmu backward, the mirror kit, one involution, two
  exchanges, one associativity).
* GADGET-DELTA (`lcoGadgetsFuseOverCopy`): `(wire | delta) ; (gadget(a) | wire) ;
  (wire | gadget(b)) ~ gadget(a + b) ; (delta | wire)` — SCALE-FUSION at the window, the
  copy-tree kit (`lcoCopyTreeAbsorbsMidSwap`: the four-leaf copy tree absorbs a middle
  crossing through three coassociativity fires and one cocommutativity fire — the dual of
  the add-tree kill), and the FIVE-STRAND COPY-ROUTE ALIGNMENT.
* THE CORES: `lcoMuFanDuplication` and `lcoDeltaFanFusion` — source-climb inductions whose
  rungs fire the padded gadget lemma, the below-padded induction hypothesis, and the
  Godement block slide between the fresh gadget and the shorter fan.

## The flips (per the commission's supersession discipline)

`lstMuFanDuplicationStatement` and `lstDeltaFanFusionStatement` are INHABITED
(`lcoMuFanDuplicationHolds` / `lcoDeltaFanFusionHolds` — ascriptions against the live
Props verbatim).  The owner Bools in `StaircaseCompleteness` stay byte-intact false as
frozen history; the inhabitants supersede them.  `lstCrossingTwoFanSwapStatement` stays
OPEN (not walled): one genuinely-burned attack is recorded at
`lcoCrossingTwoFanSwapProved`, the wall threshold is three.  The full canonical reduction
and `fxLafontStrictLayer_hasCanonicalCompleteness` stay untouched-false — the assembly
waits on the crossing core.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; audit twin with per-decl
`#assert_no_axioms` plus an independent `#print axioms` probe. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.LafontProp

/-! ## Chunk 1: the derived-row kit -/

/-- S1 kill at zero pads: a doubled crossing before any suffix dies. -/
theorem lcoTauPairDiesBare (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 2
      ([SldCell.crossing] :: [SldCell.crossing] :: suffixLayers) suffixLayers :=
  SldAreConvertibleLayers.fromSwapInvolutionRow 0 0 suffixLayers

/-- S1 kill under one wire above. -/
theorem lcoTauPairDiesUnderWire (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing] :: [SldCell.wire, SldCell.crossing] :: suffixLayers)
      suffixLayers :=
  SldAreConvertibleLayers.fromSwapInvolutionRow 1 0 suffixLayers

/-- S1 kill over one wire below. -/
theorem lcoTauPairDiesOverWire (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 3
      ([SldCell.crossing, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: suffixLayers)
      suffixLayers :=
  SldAreConvertibleLayers.fromSwapInvolutionRow 0 1 suffixLayers

/-- MIRROR-Ndelta (the copy cell crosses DOWN past a parked strand, mirror orientation of the
Ndelta row): `(delta | w) ; (w | tau) ; (tau | w) ~ tau ; (w | delta)`. -/
theorem lcoCopySlidesBelowParkedStrand (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 2
      ([SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.crossing, SldCell.wire] :: suffixLayers)
      ([SldCell.crossing] :: [SldCell.wire, SldCell.generatorDelta] :: suffixLayers) := by
  have tauPairMaterializes : SldAreConvertibleLayers 2
      ([SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.crossing, SldCell.wire] :: suffixLayers)
      ([SldCell.crossing] :: [SldCell.crossing]
        :: [SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.crossing, SldCell.wire] :: suffixLayers) :=
    SldAreConvertibleLayers.fromSymmetry
      (lcoTauPairDiesBare
        ([SldCell.generatorDelta, SldCell.wire]
          :: [SldCell.wire, SldCell.crossing]
          :: [SldCell.crossing, SldCell.wire] :: suffixLayers))
  have ndeltaFires : SldAreConvertibleLayers 2
      ([SldCell.crossing] :: [SldCell.crossing]
        :: [SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.crossing, SldCell.wire] :: suffixLayers)
      ([SldCell.crossing] :: [SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.crossing, SldCell.wire] :: suffixLayers) :=
    SldAreConvertibleLayers.underLayerPrefix 2 [SldCell.crossing]
      (SldAreConvertibleLayers.fromCopyPastSwapRow 0 0
        ([SldCell.wire, SldCell.crossing]
          :: [SldCell.crossing, SldCell.wire] :: suffixLayers))
  have innerTauPairDies : SldAreConvertibleLayers 2
      ([SldCell.crossing] :: [SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.crossing, SldCell.wire] :: suffixLayers)
      ([SldCell.crossing] :: [SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire] :: suffixLayers) :=
    sldConvUnderPrefixList
      [[SldCell.crossing], [SldCell.wire, SldCell.generatorDelta],
        [SldCell.crossing, SldCell.wire]] 2 _ _
      (lcoTauPairDiesUnderWire ([SldCell.crossing, SldCell.wire] :: suffixLayers))
  have outerTauPairDies : SldAreConvertibleLayers 2
      ([SldCell.crossing] :: [SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire] :: suffixLayers)
      ([SldCell.crossing] :: [SldCell.wire, SldCell.generatorDelta] :: suffixLayers) :=
    sldConvUnderPrefixList
      [[SldCell.crossing], [SldCell.wire, SldCell.generatorDelta]] 2 _ _
      (lcoTauPairDiesOverWire suffixLayers)
  exact SldAreConvertibleLayers.fromTransitivity tauPairMaterializes
    (SldAreConvertibleLayers.fromTransitivity ndeltaFires
      (SldAreConvertibleLayers.fromTransitivity innerTauPairDies outerTauPairDies))

/-- MIRROR-Nmu (the add cell crosses DOWN past a parked strand):
`(tau | w) ; (w | tau) ; (mu | w) ~ (w | mu) ; tau`. -/
theorem lcoAddSlidesBelowParkedStrand (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 3
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire] :: suffixLayers)
      ([SldCell.wire, SldCell.generatorMu] :: [SldCell.crossing] :: suffixLayers) := by
  have tauPairMaterializes : SldAreConvertibleLayers 3
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire] :: suffixLayers)
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire]
        :: [SldCell.crossing] :: [SldCell.crossing] :: suffixLayers) :=
    sldConvUnderPrefixList
      [[SldCell.crossing, SldCell.wire], [SldCell.wire, SldCell.crossing],
        [SldCell.generatorMu, SldCell.wire]] 3 _ _
      (SldAreConvertibleLayers.fromSymmetry (lcoTauPairDiesBare suffixLayers))
  have nmuFires : SldAreConvertibleLayers 3
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire]
        :: [SldCell.crossing] :: [SldCell.crossing] :: suffixLayers)
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers) :=
    sldConvUnderPrefixList
      [[SldCell.crossing, SldCell.wire], [SldCell.wire, SldCell.crossing]] 3 _ _
      (SldAreConvertibleLayers.fromSwapPastAddRow 0 0 ([SldCell.crossing] :: suffixLayers))
  have innerTauPairDies : SldAreConvertibleLayers 3
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers)
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers) :=
    SldAreConvertibleLayers.underLayerPrefix 3 [SldCell.crossing, SldCell.wire]
      (lcoTauPairDiesUnderWire
        ([SldCell.crossing, SldCell.wire]
          :: [SldCell.wire, SldCell.generatorMu]
          :: [SldCell.crossing] :: suffixLayers))
  have outerTauPairDies : SldAreConvertibleLayers 3
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers)
      ([SldCell.wire, SldCell.generatorMu] :: [SldCell.crossing] :: suffixLayers) :=
    lcoTauPairDiesOverWire
      ([SldCell.wire, SldCell.generatorMu] :: [SldCell.crossing] :: suffixLayers)
  exact SldAreConvertibleLayers.fromTransitivity tauPairMaterializes
    (SldAreConvertibleLayers.fromTransitivity nmuFires
      (SldAreConvertibleLayers.fromTransitivity innerTauPairDies outerTauPairDies))

/-- MIRROR-Neps (the discard cell crosses UP past a parked strand):
`(eps | w) ~ tau ; (w | eps)`. -/
theorem lcoDiscardClimbsAcrossParkedStrand (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 2
      ([SldCell.generatorEpsilon, SldCell.wire] :: suffixLayers)
      ([SldCell.crossing] :: [SldCell.wire, SldCell.generatorEpsilon] :: suffixLayers) := by
  have tauPairMaterializes : SldAreConvertibleLayers 2
      ([SldCell.generatorEpsilon, SldCell.wire] :: suffixLayers)
      ([SldCell.crossing] :: [SldCell.crossing]
        :: [SldCell.generatorEpsilon, SldCell.wire] :: suffixLayers) :=
    SldAreConvertibleLayers.fromSymmetry
      (lcoTauPairDiesBare ([SldCell.generatorEpsilon, SldCell.wire] :: suffixLayers))
  have nepsFires : SldAreConvertibleLayers 2
      ([SldCell.crossing] :: [SldCell.crossing]
        :: [SldCell.generatorEpsilon, SldCell.wire] :: suffixLayers)
      ([SldCell.crossing] :: [SldCell.wire, SldCell.generatorEpsilon] :: suffixLayers) :=
    SldAreConvertibleLayers.underLayerPrefix 2 [SldCell.crossing]
      (SldAreConvertibleLayers.fromDiscardPastSwapRow 0 0 suffixLayers)
  exact SldAreConvertibleLayers.fromTransitivity tauPairMaterializes nepsFires

/-- MIRROR-Neta (the zero cell crosses DOWN past a parked strand):
`(eta | w) ~ (w | eta) ; tau`. -/
theorem lcoZeroSlidesBelowParkedStrand (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 1
      ([SldCell.generatorEta, SldCell.wire] :: suffixLayers)
      ([SldCell.wire, SldCell.generatorEta] :: [SldCell.crossing] :: suffixLayers) := by
  have tauPairMaterializes : SldAreConvertibleLayers 1
      ([SldCell.generatorEta, SldCell.wire] :: suffixLayers)
      ([SldCell.generatorEta, SldCell.wire]
        :: [SldCell.crossing] :: [SldCell.crossing] :: suffixLayers) :=
    SldAreConvertibleLayers.underLayerPrefix 1 [SldCell.generatorEta, SldCell.wire]
      (SldAreConvertibleLayers.fromSymmetry (lcoTauPairDiesBare suffixLayers))
  have netaFires : SldAreConvertibleLayers 1
      ([SldCell.generatorEta, SldCell.wire]
        :: [SldCell.crossing] :: [SldCell.crossing] :: suffixLayers)
      ([SldCell.wire, SldCell.generatorEta] :: [SldCell.crossing] :: suffixLayers) :=
    SldAreConvertibleLayers.fromSwapPastZeroRow 0 0 ([SldCell.crossing] :: suffixLayers)
  exact SldAreConvertibleLayers.fromTransitivity tauPairMaterializes netaFires

/-! ### Pad-window composition helpers -/

/-- A pad window over a below-padded block widens the below pad. -/
theorem lcoPadWindowOfPadLayersBelow (padAboveCount padBelowCount extraCount : Nat) :
    (windowLayers : List SldLayer) ->
    sldPadWindow padAboveCount padBelowCount (sldPadLayersBelow extraCount windowLayers)
      = sldPadWindow padAboveCount (extraCount + padBelowCount) windowLayers
  | [] => rfl
  | headLayer :: tailLayers => by
      show sldPadLayer padAboveCount padBelowCount
          (sldAppendCells headLayer (sldWireLayerOfArity extraCount))
          :: sldPadWindow padAboveCount padBelowCount
              (sldPadLayersBelow extraCount tailLayers)
        = sldPadLayer padAboveCount (extraCount + padBelowCount) headLayer
          :: sldPadWindow padAboveCount (extraCount + padBelowCount) tailLayers
      rw [lcoPadWindowOfPadLayersBelow padAboveCount padBelowCount extraCount tailLayers]
      show sldAppendCells (sldWireLayerOfArity padAboveCount)
          (sldAppendCells (sldAppendCells headLayer (sldWireLayerOfArity extraCount))
            (sldWireLayerOfArity padBelowCount)) :: _
        = sldAppendCells (sldWireLayerOfArity padAboveCount)
            (sldAppendCells headLayer (sldWireLayerOfArity (extraCount + padBelowCount))) :: _
      rw [sldAppendCellsAssoc headLayer (sldWireLayerOfArity extraCount)
        (sldWireLayerOfArity padBelowCount), sldWireLayerSplitsAtCount]

/-- A pad window over an above-padded block widens the above pad. -/
theorem lcoPadWindowOfPadLayersAbove (padAboveCount extraCount padBelowCount : Nat) :
    (windowLayers : List SldLayer) ->
    sldPadWindow padAboveCount padBelowCount (sldPadLayersAbove extraCount windowLayers)
      = sldPadWindow (padAboveCount + extraCount) padBelowCount windowLayers
  | [] => rfl
  | headLayer :: tailLayers => by
      show sldPadLayer padAboveCount padBelowCount
          (sldAppendCells (sldWireLayerOfArity extraCount) headLayer)
          :: sldPadWindow padAboveCount padBelowCount
              (sldPadLayersAbove extraCount tailLayers)
        = sldPadLayer (padAboveCount + extraCount) padBelowCount headLayer
          :: sldPadWindow (padAboveCount + extraCount) padBelowCount tailLayers
      rw [lcoPadWindowOfPadLayersAbove padAboveCount extraCount padBelowCount tailLayers]
      show sldAppendCells (sldWireLayerOfArity padAboveCount)
          (sldAppendCells (sldAppendCells (sldWireLayerOfArity extraCount) headLayer)
            (sldWireLayerOfArity padBelowCount)) :: _
        = sldAppendCells (sldWireLayerOfArity (padAboveCount + extraCount))
            (sldAppendCells headLayer (sldWireLayerOfArity padBelowCount)) :: _
      rw [sldAppendCellsAssoc (sldWireLayerOfArity extraCount) headLayer
        (sldWireLayerOfArity padBelowCount),
        (sldAppendCellsAssoc (sldWireLayerOfArity padAboveCount)
          (sldWireLayerOfArity extraCount)
          (sldAppendCells headLayer (sldWireLayerOfArity padBelowCount))).symm,
        sldWireLayerSplitsAtCount]

/-- Pad windows distribute over layer-list append. -/
theorem lcoPadWindowOfAppendLayers (padAboveCount padBelowCount : Nat) :
    (firstLayers secondLayers : List SldLayer) ->
    sldPadWindow padAboveCount padBelowCount (sldAppendLayers firstLayers secondLayers)
      = sldAppendLayers (sldPadWindow padAboveCount padBelowCount firstLayers)
          (sldPadWindow padAboveCount padBelowCount secondLayers)
  | [], _ => rfl
  | headLayer :: tailLayers, secondLayers =>
      congrArg (fun restLayers =>
        sldPadLayer padAboveCount padBelowCount headLayer :: restLayers)
        (lcoPadWindowOfAppendLayers padAboveCount padBelowCount tailLayers secondLayers)

/-- TWO-SIDED PAD CONGRUENCE: a conversion survives a pad window (below pad then above pad,
refolded through the template's window identities). -/
theorem lcoConvPadsWindow {boundaryArity : Nat} {leftLayers rightLayers : List SldLayer}
    (areConvertible : SldAreConvertibleLayers boundaryArity leftLayers rightLayers)
    (padAboveCount padBelowCount : Nat) :
    SldAreConvertibleLayers (padAboveCount + (boundaryArity + padBelowCount))
      (sldPadWindow padAboveCount padBelowCount leftLayers)
      (sldPadWindow padAboveCount padBelowCount rightLayers) := by
  have bothPadded := sldConvPadsAbove (sldConvPadsBelow areConvertible padBelowCount)
    padAboveCount
  rw [lstPadAboveOfPadBelowIsPadWindow, lstPadAboveOfPadBelowIsPadWindow] at bothPadded
  exact bothPadded


/-! ## Chunk 2: SCALE-TAU — the crossing slides through a scale tower -/

/-- SCALE-TAU: a scale tower on the upper strand followed by the crossing converts to the
crossing followed by the tower on the lower strand — the naturality of tau against the whole
tower, by induction riding the successor unfold (Nmu at the merge, the fresh zero via Neta,
the discard via mirror-Neps, the copy via mirror-Ndelta). -/
theorem lcoScaleTowerCrossesDown : (scaleFactor : Nat) ->
    SldAreConvertibleLayers 2
      (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactor))
        [[SldCell.crossing]])
      ([SldCell.crossing] :: sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
  | 0 => by
      rw [lstScaleZeroLayerShape]
      have netaFires : SldAreConvertibleLayers 2
          ([SldCell.generatorEpsilon, SldCell.wire]
            :: [SldCell.generatorEta, SldCell.wire] :: [SldCell.crossing] :: [])
          ([SldCell.generatorEpsilon, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorEta] :: []) :=
        SldAreConvertibleLayers.underLayerPrefix 2
          [SldCell.generatorEpsilon, SldCell.wire]
          (SldAreConvertibleLayers.fromSwapPastZeroRow 0 0 [])
      have discardClimbs : SldAreConvertibleLayers 2
          ([SldCell.generatorEpsilon, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorEta] :: [])
          ([SldCell.crossing] :: [SldCell.wire, SldCell.generatorEpsilon]
            :: [SldCell.wire, SldCell.generatorEta] :: []) :=
        lcoDiscardClimbsAcrossParkedStrand ([SldCell.wire, SldCell.generatorEta] :: [])
      exact SldAreConvertibleLayers.fromTransitivity netaFires discardClimbs
  | scaleFactorPred + 1 => by
      rw [lstScaleSuccUnfolds scaleFactorPred]
      have leftShape : sldPadLayersBelow 1
          (sldAppendLayers [[SldCell.generatorDelta]]
            (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
              [[SldCell.generatorMu]]))
          = [SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu, SldCell.wire]] := by
        rw [sldPadLayersBelowOfAppend, sldPadLayersBelowOfAppend, lstPadLayersBelowCompose]
        rfl
      have rightShape : sldPadLayersAbove 1
          (sldAppendLayers [[SldCell.generatorDelta]]
            (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
              [[SldCell.generatorMu]]))
          = [SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
                [[SldCell.wire, SldCell.generatorMu]] := by
        rw [sldPadLayersAboveOfAppend, sldPadLayersAboveOfAppend,
          lstPadAboveOfPadBelowIsPadWindow]
        rfl
      rw [leftShape, rightShape]
      show SldAreConvertibleLayers 2
        ([SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers
              (sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu, SldCell.wire]])
              [[SldCell.crossing]])
        ([SldCell.crossing] :: [SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
              [[SldCell.wire, SldCell.generatorMu]])
      rw [sldAppendLayersAssoc]
      have prefixReach : sldLayersTargetArityFrom 2
          ([SldCell.generatorDelta, SldCell.wire]
            :: sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred)) = 3 := by
        show sldLayersTargetArityFrom 3
          (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred)) = 3
        have liftedReach := sldPadLayersBelowTargetArityFrom 2
          (lstScaleLayerList scaleFactorPred) 1
        rw [lstScaleLayersReach] at liftedReach
        exact liftedReach
      have nmuFires : SldAreConvertibleLayers 2
          ([SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))
          ([SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.crossing] :: [SldCell.crossing, SldCell.wire]
                  :: [SldCell.wire, SldCell.generatorMu] :: [])) := by
        refine sldConvUnderPrefixList
          ([SldCell.generatorDelta, SldCell.wire]
            :: sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred)) 2 _ _ ?_
        rw [prefixReach]
        exact SldAreConvertibleLayers.fromSwapPastAddRow 0 0 []
      have tauSlidesUp : SldAreConvertibleLayers 2
          ([SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.crossing] :: [SldCell.crossing, SldCell.wire]
                  :: [SldCell.wire, SldCell.generatorMu] :: []))
          ([SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                ([SldCell.crossing, SldCell.wire]
                  :: [SldCell.wire, SldCell.generatorMu] :: [])) := by
        have slideInstance := sldLowerLayerSlidesDownPastBlock [SldCell.crossing]
          (lstScaleLayerList scaleFactorPred) 1
          (lstScaleLayersAreComposable scaleFactorPred)
          ([SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu] :: [])
        rw [lstScaleLayersReach] at slideInstance
        exact SldAreConvertibleLayers.underLayerPrefix 2
          [SldCell.generatorDelta, SldCell.wire]
          (SldAreConvertibleLayers.fromSymmetry slideInstance)
      have paddedRecursion : SldAreConvertibleLayers 3
          (sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
            ([SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu] :: []))
          ([SldCell.crossing, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.generatorMu] :: [])) := by
        have belowPadded := sldConvPadsBelow (lcoScaleTowerCrossesDown scaleFactorPred) 1
        rw [sldPadLayersBelowOfAppend, lstPadLayersBelowCompose,
          show sldPadLayersBelow 1
              ([SldCell.crossing] :: sldPadLayersAbove 1 (lstScaleLayerList scaleFactorPred))
            = [SldCell.crossing, SldCell.wire]
              :: sldPadLayersBelow 1
                  (sldPadLayersAbove 1 (lstScaleLayerList scaleFactorPred)) from rfl,
          lstPadBelowOfPadAboveIsPadWindow] at belowPadded
        have withSuffix := sldConvAppendsSuffix belowPadded
          ([SldCell.wire, SldCell.generatorMu] :: [])
        rw [sldAppendLayersAssoc] at withSuffix
        exact withSuffix
      have recursionUnderPrefix : SldAreConvertibleLayers 2
          ([SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                ([SldCell.crossing, SldCell.wire]
                  :: [SldCell.wire, SldCell.generatorMu] :: []))
          ([SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing]
            :: [SldCell.crossing, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.generatorMu] :: [])) :=
        sldConvUnderPrefixList
          [[SldCell.generatorDelta, SldCell.wire], [SldCell.wire, SldCell.crossing]] 2 _ _
          paddedRecursion
      have copySlides : SldAreConvertibleLayers 2
          ([SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing]
            :: [SldCell.crossing, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.generatorMu] :: []))
          ([SldCell.crossing] :: [SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.generatorMu] :: [])) :=
        lcoCopySlidesBelowParkedStrand
          (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
            ([SldCell.wire, SldCell.generatorMu] :: []))
      exact SldAreConvertibleLayers.fromTransitivity nmuFires
        (SldAreConvertibleLayers.fromTransitivity tauSlidesUp
          (SldAreConvertibleLayers.fromTransitivity recursionUnderPrefix copySlides))

/-- SCALE-TAU mirror: the crossing followed by the tower on the lower strand, read the other
way — the tower enters from below. -/
theorem lcoSwapDescendsIntoScaleTower (scaleFactor : Nat) :
    SldAreConvertibleLayers 2
      ([SldCell.crossing] :: sldPadLayersBelow 1 (lstScaleLayerList scaleFactor))
      (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
        [[SldCell.crossing]]) := by
  have tauPairAppends : SldAreConvertibleLayers 2
      ([SldCell.crossing] :: sldPadLayersBelow 1 (lstScaleLayerList scaleFactor))
      ([SldCell.crossing]
        :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactor))
            ([SldCell.crossing] :: [SldCell.crossing] :: [])) := by
    have padReach : sldLayersTargetArityFrom 2
        (sldPadLayersBelow 1 (lstScaleLayerList scaleFactor)) = 2 := by
      have liftedReach := sldPadLayersBelowTargetArityFrom 1
        (lstScaleLayerList scaleFactor) 1
      rw [lstScaleLayersReach] at liftedReach
      exact liftedReach
    have appendedForm : SldAreConvertibleLayers 2
        (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactor)) [])
        (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactor))
          ([SldCell.crossing] :: [SldCell.crossing] :: [])) := by
      refine sldConvUnderPrefixList
        (sldPadLayersBelow 1 (lstScaleLayerList scaleFactor)) 2 _ _ ?_
      rw [padReach]
      exact SldAreConvertibleLayers.fromSymmetry (lcoTauPairDiesBare [])
    rw [sldAppendLayersNilRightIsSelf] at appendedForm
    exact SldAreConvertibleLayers.underLayerPrefix 2 [SldCell.crossing] appendedForm
  have scaleTauWithSuffix : SldAreConvertibleLayers 2
      ([SldCell.crossing]
        :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactor))
            ([SldCell.crossing] :: [SldCell.crossing] :: []))
      ([SldCell.crossing] :: [SldCell.crossing]
        :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
            ([SldCell.crossing] :: [])) := by
    have withSuffix := sldConvAppendsSuffix (lcoScaleTowerCrossesDown scaleFactor)
      ([SldCell.crossing] :: [])
    rw [sldAppendLayersAssoc] at withSuffix
    exact SldAreConvertibleLayers.underLayerPrefix 2 [SldCell.crossing] withSuffix
  have tauPairDies : SldAreConvertibleLayers 2
      ([SldCell.crossing] :: [SldCell.crossing]
        :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
            ([SldCell.crossing] :: []))
      (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
        ([SldCell.crossing] :: [])) :=
    lcoTauPairDiesBare
      (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
        ([SldCell.crossing] :: []))
  exact SldAreConvertibleLayers.fromTransitivity tauPairAppends
    (SldAreConvertibleLayers.fromTransitivity scaleTauWithSuffix tauPairDies)


/-! ## The four-strand add-tree kit -/

/-- Reassociation of the balanced four-strand add tree into the left-leaning tree
(exchange + two associativity fires). -/
theorem lcoBalancedAddTreeLeansLeft (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 4
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu] :: suffixLayers)
      ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire]
        :: [SldCell.generatorMu] :: suffixLayers) := by
  have addsExchange : SldAreConvertibleLayers 4
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu] :: suffixLayers)
      ([SldCell.wire, SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu, SldCell.wire]
        :: [SldCell.generatorMu] :: suffixLayers) :=
    sldDisjointLayersExchange [SldCell.generatorMu] [SldCell.generatorMu]
      ([SldCell.generatorMu] :: suffixLayers)
  have assocUnderDeepAdd : SldAreConvertibleLayers 4
      ([SldCell.wire, SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu, SldCell.wire]
        :: [SldCell.generatorMu] :: suffixLayers)
      ([SldCell.wire, SldCell.wire, SldCell.generatorMu]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu] :: suffixLayers) :=
    SldAreConvertibleLayers.underLayerPrefix 4
      [SldCell.wire, SldCell.wire, SldCell.generatorMu]
      (SldAreConvertibleLayers.fromAddAssociativityRow 0 0 suffixLayers)
  have assocUnderMidAdd : SldAreConvertibleLayers 4
      ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire]
        :: [SldCell.generatorMu] :: suffixLayers)
      ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu] :: suffixLayers) :=
    SldAreConvertibleLayers.underLayerPrefix 4
      [SldCell.wire, SldCell.generatorMu, SldCell.wire]
      (SldAreConvertibleLayers.fromAddAssociativityRow 0 0 suffixLayers)
  have assocAtPad : SldAreConvertibleLayers 4
      ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu] :: suffixLayers)
      ([SldCell.wire, SldCell.wire, SldCell.generatorMu]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu] :: suffixLayers) :=
    SldAreConvertibleLayers.fromAddAssociativityRow 1 0
      ([SldCell.generatorMu] :: suffixLayers)
  exact SldAreConvertibleLayers.fromTransitivity addsExchange
    (SldAreConvertibleLayers.fromTransitivity assocUnderDeepAdd
      (SldAreConvertibleLayers.fromTransitivity
        (SldAreConvertibleLayers.fromSymmetry assocAtPad)
        (SldAreConvertibleLayers.fromSymmetry assocUnderMidAdd)))

/-- The middle crossing dies against the balanced four-strand add tree (lean the tree left,
fire commutativity at the padded middle add, lean back). -/
theorem lcoMidSwapDiesAgainstAddTree (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 4
      ([SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu] :: suffixLayers)
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu] :: suffixLayers) := by
  have treeLeansUnderSwap : SldAreConvertibleLayers 4
      ([SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu] :: suffixLayers)
      ([SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire]
        :: [SldCell.generatorMu] :: suffixLayers) :=
    SldAreConvertibleLayers.underLayerPrefix 4
      [SldCell.wire, SldCell.crossing, SldCell.wire]
      (lcoBalancedAddTreeLeansLeft suffixLayers)
  have commutativityFires : SldAreConvertibleLayers 4
      ([SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire]
        :: [SldCell.generatorMu] :: suffixLayers)
      ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire]
        :: [SldCell.generatorMu] :: suffixLayers) :=
    SldAreConvertibleLayers.fromAddCommutativityRow 1 1
      ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: suffixLayers)
  exact SldAreConvertibleLayers.fromTransitivity treeLeansUnderSwap
    (SldAreConvertibleLayers.fromTransitivity commutativityFires
      (SldAreConvertibleLayers.fromSymmetry (lcoBalancedAddTreeLeansLeft suffixLayers)))

/-! ## SCALE-MU: the scale tower distributes over the add -/

/-- SCALE-MU: adding then scaling converts to scaling both summands then adding —
`mu ; scale(s) ~ (scale(s) | wire) ; (wire | scale(s)) ; mu` (the derivation
`s * (x + y) = s * x + s * y`).  Zero case: B3 splits the discard; successor case: B1 opens
the square, the two copies split, the IH distributes the shorter tower, the emitted crossing
dies against the add tree. -/
theorem lcoScaleTowerDistributesOverAdd : (scaleFactor : Nat) ->
    SldAreConvertibleLayers 2
      ([SldCell.generatorMu] :: lstScaleLayerList scaleFactor)
      (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactor))
        (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
          [[SldCell.generatorMu]]))
  | 0 => by
      rw [lstScaleZeroLayerShape]
      have discardSplits : SldAreConvertibleLayers 2
          ([SldCell.generatorMu] :: [SldCell.generatorEpsilon]
            :: [SldCell.generatorEta] :: [])
          ([SldCell.generatorEpsilon, SldCell.generatorEpsilon]
            :: [SldCell.generatorEta] :: []) :=
        SldAreConvertibleLayers.fromDiscardAfterAddRow 0 0 ([SldCell.generatorEta] :: [])
      have discardPairSplits : SldAreConvertibleLayers 2
          ([SldCell.generatorEpsilon, SldCell.generatorEpsilon]
            :: [SldCell.generatorEta] :: [])
          ([SldCell.generatorEpsilon, SldCell.wire] :: [SldCell.generatorEpsilon]
            :: [SldCell.generatorEta] :: []) :=
        SldAreConvertibleLayers.layerSplitTopActsFirst [SldCell.generatorEpsilon]
          [SldCell.generatorEpsilon] ([SldCell.generatorEta] :: [])
      have zeroDiscardExchange : SldAreConvertibleLayers 2
          ([SldCell.generatorEpsilon, SldCell.wire]
            :: [SldCell.generatorEta, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorEpsilon]
            :: [SldCell.wire, SldCell.generatorEta]
            :: [SldCell.generatorMu] :: [])
          ([SldCell.generatorEpsilon, SldCell.wire]
            :: [SldCell.generatorEpsilon]
            :: [SldCell.generatorEta]
            :: [SldCell.wire, SldCell.generatorEta]
            :: [SldCell.generatorMu] :: []) :=
        SldAreConvertibleLayers.underLayerPrefix 2
          [SldCell.generatorEpsilon, SldCell.wire]
          (sldDisjointLayersExchange [SldCell.generatorEta] [SldCell.generatorEpsilon]
            ([SldCell.wire, SldCell.generatorEta] :: [SldCell.generatorMu] :: []))
      have rightUnitFires : SldAreConvertibleLayers 2
          ([SldCell.generatorEpsilon, SldCell.wire]
            :: [SldCell.generatorEpsilon]
            :: [SldCell.generatorEta]
            :: [SldCell.wire, SldCell.generatorEta]
            :: [SldCell.generatorMu] :: [])
          ([SldCell.generatorEpsilon, SldCell.wire]
            :: [SldCell.generatorEpsilon]
            :: [SldCell.generatorEta] :: []) :=
        sldConvUnderPrefixList
          [[SldCell.generatorEpsilon, SldCell.wire], [SldCell.generatorEpsilon],
            [SldCell.generatorEta]] 2 _ _
          (SldAreConvertibleLayers.fromAddRightUnitRow 0 0 [])
      exact SldAreConvertibleLayers.fromTransitivity discardSplits
        (SldAreConvertibleLayers.fromTransitivity discardPairSplits
          (SldAreConvertibleLayers.fromSymmetry
            (SldAreConvertibleLayers.fromTransitivity zeroDiscardExchange rightUnitFires)))
  | scaleFactorPred + 1 => by
      rw [lstScaleSuccUnfolds scaleFactorPred]
      have leftShape : sldPadLayersBelow 1
          (sldAppendLayers [[SldCell.generatorDelta]]
            (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
              [[SldCell.generatorMu]]))
          = [SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu, SldCell.wire]] := by
        rw [sldPadLayersBelowOfAppend, sldPadLayersBelowOfAppend, lstPadLayersBelowCompose]
        rfl
      have rightShape : sldPadLayersAbove 1
          (sldAppendLayers [[SldCell.generatorDelta]]
            (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
              [[SldCell.generatorMu]]))
          = [SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
                [[SldCell.wire, SldCell.generatorMu]] := by
        rw [sldPadLayersAboveOfAppend, sldPadLayersAboveOfAppend,
          lstPadAboveOfPadBelowIsPadWindow]
        rfl
      rw [leftShape, rightShape]
      show SldAreConvertibleLayers 2
        ([SldCell.generatorMu] :: [SldCell.generatorDelta]
          :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
              [[SldCell.generatorMu]])
        ([SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers
              (sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu, SldCell.wire]])
              ([SldCell.wire, SldCell.generatorDelta]
                :: sldAppendLayers
                    (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
                      [[SldCell.wire, SldCell.generatorMu]])
                    [[SldCell.generatorMu]]))
      rw [sldAppendLayersAssoc (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
          [[SldCell.generatorMu, SldCell.wire]],
        sldAppendLayersAssoc (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
          [[SldCell.wire, SldCell.generatorMu]] [[SldCell.generatorMu]]]
      -- Left spine: B1, split the double add, slide the deep add below the tower, padded IH.
      have bimonoidFires : SldAreConvertibleLayers 2
          ([SldCell.generatorMu] :: [SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu]])
          ([SldCell.generatorDelta, SldCell.generatorDelta]
            :: [SldCell.wire, SldCell.crossing, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.generatorMu]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu]]) :=
        SldAreConvertibleLayers.fromBimonoidSquareRow 0 0
          (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
            [[SldCell.generatorMu]])
      have doubleAddSplits : SldAreConvertibleLayers 2
          ([SldCell.generatorDelta, SldCell.generatorDelta]
            :: [SldCell.wire, SldCell.crossing, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.generatorMu]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu]])
          ([SldCell.generatorDelta, SldCell.generatorDelta]
            :: [SldCell.wire, SldCell.crossing, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorMu]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu]]) :=
        sldConvUnderPrefixList
          [[SldCell.generatorDelta, SldCell.generatorDelta],
            [SldCell.wire, SldCell.crossing, SldCell.wire]] 2 _ _
          (SldAreConvertibleLayers.layerSplitTopActsFirst [SldCell.generatorMu]
            [SldCell.generatorMu]
            (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
              [[SldCell.generatorMu]]))
      have deepAddSlides : SldAreConvertibleLayers 2
          ([SldCell.generatorDelta, SldCell.generatorDelta]
            :: [SldCell.wire, SldCell.crossing, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorMu]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu]])
          ([SldCell.generatorDelta, SldCell.generatorDelta]
            :: [SldCell.wire, SldCell.crossing, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.generatorMu] :: [SldCell.generatorMu] :: [])) := by
        have slideInstance := sldLowerLayerSlidesDownPastBlock [SldCell.generatorMu]
          (lstScaleLayerList scaleFactorPred) 1
          (lstScaleLayersAreComposable scaleFactorPred) [[SldCell.generatorMu]]
        rw [lstScaleLayersReach] at slideInstance
        exact sldConvUnderPrefixList
          [[SldCell.generatorDelta, SldCell.generatorDelta],
            [SldCell.wire, SldCell.crossing, SldCell.wire],
            [SldCell.generatorMu, SldCell.wire, SldCell.wire]] 2 _ _ slideInstance
      have paddedRecursion : SldAreConvertibleLayers 4
          ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.generatorMu] :: [SldCell.generatorMu] :: []))
          (sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
            (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactorPred))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu] :: []))) := by
        have belowPadded := sldConvPadsBelow
          (lcoScaleTowerDistributesOverAdd scaleFactorPred) 2
        rw [sldPadLayersBelowOfAppend, sldPadLayersBelowOfAppend,
          lstPadLayersBelowCompose, lstPadBelowOfPadAboveIsPadWindow] at belowPadded
        have withSuffix := sldConvAppendsSuffix belowPadded
          ([SldCell.wire, SldCell.generatorMu] :: [SldCell.generatorMu] :: [])
        rw [sldAppendLayersAssoc, sldAppendLayersAssoc] at withSuffix
        exact withSuffix
      have recursionUnderPrefix : SldAreConvertibleLayers 2
          ([SldCell.generatorDelta, SldCell.generatorDelta]
            :: [SldCell.wire, SldCell.crossing, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.generatorMu] :: [SldCell.generatorMu] :: []))
          ([SldCell.generatorDelta, SldCell.generatorDelta]
            :: [SldCell.wire, SldCell.crossing, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactorPred))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.generatorMu]
                    :: [SldCell.generatorMu] :: []))) :=
        sldConvUnderPrefixList
          [[SldCell.generatorDelta, SldCell.generatorDelta],
            [SldCell.wire, SldCell.crossing, SldCell.wire]] 2 _ _ paddedRecursion
      -- Head surgery: split the double copy, slide the crossing below the first tower,
      -- convert the crossing through the second tower, kill it against the add tree.
      have doubleCopySplits : SldAreConvertibleLayers 2
          ([SldCell.generatorDelta, SldCell.generatorDelta]
            :: [SldCell.wire, SldCell.crossing, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactorPred))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.generatorMu]
                    :: [SldCell.generatorMu] :: [])))
          ([SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: [SldCell.wire, SldCell.crossing, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactorPred))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.generatorMu]
                    :: [SldCell.generatorMu] :: []))) :=
        SldAreConvertibleLayers.layerSplitTopActsFirst [SldCell.generatorDelta]
          [SldCell.generatorDelta]
          ([SldCell.wire, SldCell.crossing, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactorPred))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.generatorMu]
                    :: [SldCell.generatorMu] :: [])))
      have midSwapSlides : SldAreConvertibleLayers 2
          ([SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: [SldCell.wire, SldCell.crossing, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactorPred))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.generatorMu]
                    :: [SldCell.generatorMu] :: [])))
          ([SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.crossing, SldCell.wire]
                  :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactorPred))
                      ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                        :: [SldCell.wire, SldCell.generatorMu]
                        :: [SldCell.generatorMu] :: []))) := by
        have slideInstance := sldLowerLayerSlidesDownPastBlock
          [SldCell.crossing, SldCell.wire] (lstScaleLayerList scaleFactorPred) 1
          (lstScaleLayersAreComposable scaleFactorPred)
          (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactorPred))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorMu]
              :: [SldCell.generatorMu] :: []))
        rw [lstScaleLayersReach] at slideInstance
        exact sldConvUnderPrefixList
          [[SldCell.generatorDelta, SldCell.wire],
            [SldCell.wire, SldCell.wire, SldCell.generatorDelta]] 2 _ _ slideInstance
      have swapThroughSecondTower : SldAreConvertibleLayers 4
          ([SldCell.wire, SldCell.crossing, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactorPred))
                ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                  :: [SldCell.wire, SldCell.generatorMu]
                  :: [SldCell.generatorMu] :: []))
          (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))
            ([SldCell.wire, SldCell.crossing, SldCell.wire]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorMu]
              :: [SldCell.generatorMu] :: [])) := by
        have windowPadded := lcoConvPadsWindow
          (lcoSwapDescendsIntoScaleTower scaleFactorPred) 1 1
        rw [show sldPadWindow 1 1
              ([SldCell.crossing]
                :: sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
            = [SldCell.wire, SldCell.crossing, SldCell.wire]
              :: sldPadWindow 1 1
                  (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred)) from rfl,
          lcoPadWindowOfPadLayersBelow, lcoPadWindowOfAppendLayers,
          lcoPadWindowOfPadLayersAbove] at windowPadded
        have withSuffix := sldConvAppendsSuffix windowPadded
          ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorMu]
            :: [SldCell.generatorMu] :: [])
        rw [sldAppendLayersAssoc] at withSuffix
        exact withSuffix
      have swapConvertsUnderPrefix : SldAreConvertibleLayers 2
          ([SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.crossing, SldCell.wire]
                  :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactorPred))
                      ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                        :: [SldCell.wire, SldCell.generatorMu]
                        :: [SldCell.generatorMu] :: [])))
          ([SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))
                  ([SldCell.wire, SldCell.crossing, SldCell.wire]
                    :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.generatorMu]
                    :: [SldCell.generatorMu] :: []))) := by
        have prefixReach : sldLayersTargetArityFrom 2
            ([SldCell.generatorDelta, SldCell.wire]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred)) = 4 := by
          show sldLayersTargetArityFrom 4
            (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred)) = 4
          have liftedReach := sldPadLayersBelowTargetArityFrom 3
            (lstScaleLayerList scaleFactorPred) 1
          rw [lstScaleLayersReach] at liftedReach
          exact liftedReach
        refine sldConvUnderPrefixList
          ([SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred)) 2 _ _ ?_
        rw [prefixReach]
        exact swapThroughSecondTower
      have swapDiesInTree : SldAreConvertibleLayers 2
          ([SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))
                  ([SldCell.wire, SldCell.crossing, SldCell.wire]
                    :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.generatorMu]
                    :: [SldCell.generatorMu] :: [])))
          ([SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.generatorMu]
                    :: [SldCell.generatorMu] :: []))) := by
        have prefixReach : sldLayersTargetArityFrom 2
            ([SldCell.generatorDelta, SldCell.wire]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                  (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))) = 4 := by
          show sldLayersTargetArityFrom 4
            (sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
              (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))) = 4
          rw [sldAppendLayersTargetArityFrom]
          have belowReachAtFour : sldLayersTargetArityFrom 4
              (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred)) = 4 := by
            have liftedReach := sldPadLayersBelowTargetArityFrom 3
              (lstScaleLayerList scaleFactorPred) 1
            rw [lstScaleLayersReach] at liftedReach
            exact liftedReach
          rw [belowReachAtFour]
          have windowReach := sldPadWindowTargetArityFrom 2 1
            (lstScaleLayerList scaleFactorPred) 1
          rw [lstScaleLayersReach] at windowReach
          exact windowReach
        have reassembled : SldAreConvertibleLayers 2
            (sldAppendLayers
              ([SldCell.generatorDelta, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
                :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                    (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred)))
              ([SldCell.wire, SldCell.crossing, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu] :: []))
            (sldAppendLayers
              ([SldCell.generatorDelta, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
                :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                    (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred)))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu] :: [])) := by
          refine sldConvUnderPrefixList
            ([SldCell.generatorDelta, SldCell.wire]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                  (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))) 2 _ _ ?_
          rw [prefixReach]
          exact lcoMidSwapDiesAgainstAddTree []
        rw [show sldAppendLayers
              ([SldCell.generatorDelta, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
                :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                    (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred)))
              ([SldCell.wire, SldCell.crossing, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu] :: [])
            = [SldCell.generatorDelta, SldCell.wire]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: sldAppendLayers
                  (sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                    (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred)))
                  ([SldCell.wire, SldCell.crossing, SldCell.wire]
                    :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.generatorMu]
                    :: [SldCell.generatorMu] :: []) from rfl,
          sldAppendLayersAssoc] at reassembled
        rw [show sldAppendLayers
              ([SldCell.generatorDelta, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
                :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                    (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred)))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu] :: [])
            = [SldCell.generatorDelta, SldCell.wire]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: sldAppendLayers
                  (sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                    (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred)))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.generatorMu]
                    :: [SldCell.generatorMu] :: []) from rfl,
          sldAppendLayersAssoc] at reassembled
        exact reassembled
      -- Right spine: exchange the first-copy add with the fresh copy, slide it below the
      -- second tower, slide the fresh copy below the first tower.
      have addCopyExchange : SldAreConvertibleLayers 2
          ([SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                ([SldCell.generatorMu, SldCell.wire]
                  :: [SldCell.wire, SldCell.generatorDelta]
                  :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
                      ([SldCell.wire, SldCell.generatorMu]
                        :: [SldCell.generatorMu] :: [])))
          ([SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                  :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
                      ([SldCell.wire, SldCell.generatorMu]
                        :: [SldCell.generatorMu] :: []))) := by
        have prefixReach : sldLayersTargetArityFrom 2
            ([SldCell.generatorDelta, SldCell.wire]
              :: sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred)) = 3 := by
          show sldLayersTargetArityFrom 3
            (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred)) = 3
          have liftedReach := sldPadLayersBelowTargetArityFrom 2
            (lstScaleLayerList scaleFactorPred) 1
          rw [lstScaleLayersReach] at liftedReach
          exact liftedReach
        refine sldConvUnderPrefixList
          ([SldCell.generatorDelta, SldCell.wire]
            :: sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred)) 2 _ _ ?_
        rw [prefixReach]
        exact sldDisjointLayersExchange [SldCell.generatorMu] [SldCell.generatorDelta]
          (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
            ([SldCell.wire, SldCell.generatorMu] :: [SldCell.generatorMu] :: []))
      have addSlidesBelowSecondTower : SldAreConvertibleLayers 4
          ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.generatorMu] :: [SldCell.generatorMu] :: []))
          (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorMu] :: [SldCell.generatorMu] :: [])) := by
        have slideInstance := sldUpperLayerSlidesDownPastBlock [SldCell.generatorMu]
          (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred)) 2
          (sldPadLayersBelowAreComposableFrom 1 (lstScaleLayerList scaleFactorPred) 1
            (lstScaleLayersAreComposable scaleFactorPred))
          ([SldCell.wire, SldCell.generatorMu] :: [SldCell.generatorMu] :: [])
        have padReach : sldLayersTargetArityFrom 2
            (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred)) = 2 := by
          have liftedReach := sldPadLayersBelowTargetArityFrom 1
            (lstScaleLayerList scaleFactorPred) 1
          rw [lstScaleLayersReach] at liftedReach
          exact liftedReach
        rw [padReach, lstPadAboveOfPadBelowIsPadWindow,
          lstPadAboveOfPadBelowIsPadWindow] at slideInstance
        exact slideInstance
      have addSlideUnderPrefix : SldAreConvertibleLayers 2
          ([SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                  :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
                      ([SldCell.wire, SldCell.generatorMu]
                        :: [SldCell.generatorMu] :: [])))
          ([SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
                  :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))
                      ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                        :: [SldCell.wire, SldCell.generatorMu]
                        :: [SldCell.generatorMu] :: []))) := by
        have prefixReach : sldLayersTargetArityFrom 2
            ([SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                  [[SldCell.wire, SldCell.wire, SldCell.generatorDelta]]) = 4 := by
          show sldLayersTargetArityFrom 3
            (sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
              [[SldCell.wire, SldCell.wire, SldCell.generatorDelta]]) = 4
          rw [sldAppendLayersTargetArityFrom]
          have belowReachAtThree : sldLayersTargetArityFrom 3
              (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred)) = 3 := by
            have liftedReach := sldPadLayersBelowTargetArityFrom 2
              (lstScaleLayerList scaleFactorPred) 1
            rw [lstScaleLayersReach] at liftedReach
            exact liftedReach
          rw [belowReachAtThree]
          rfl
        have prefixed : SldAreConvertibleLayers 2
            (sldAppendLayers
              ([SldCell.generatorDelta, SldCell.wire]
                :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                    [[SldCell.wire, SldCell.wire, SldCell.generatorDelta]])
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
                    ([SldCell.wire, SldCell.generatorMu] :: [SldCell.generatorMu] :: [])))
            (sldAppendLayers
              ([SldCell.generatorDelta, SldCell.wire]
                :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                    [[SldCell.wire, SldCell.wire, SldCell.generatorDelta]])
              (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))
                ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                  :: [SldCell.wire, SldCell.generatorMu]
                  :: [SldCell.generatorMu] :: []))) := by
          refine sldConvUnderPrefixList
            ([SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                  [[SldCell.wire, SldCell.wire, SldCell.generatorDelta]]) 2 _ _ ?_
          rw [prefixReach]
          exact addSlidesBelowSecondTower
        rw [show sldAppendLayers
              ([SldCell.generatorDelta, SldCell.wire]
                :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                    [[SldCell.wire, SldCell.wire, SldCell.generatorDelta]])
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
                    ([SldCell.wire, SldCell.generatorMu] :: [SldCell.generatorMu] :: []))
            = [SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers
                  (sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                    [[SldCell.wire, SldCell.wire, SldCell.generatorDelta]])
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactorPred))
                        ([SldCell.wire, SldCell.generatorMu]
                          :: [SldCell.generatorMu] :: [])) from rfl,
          sldAppendLayersAssoc,
          show sldAppendLayers
              ([SldCell.generatorDelta, SldCell.wire]
                :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                    [[SldCell.wire, SldCell.wire, SldCell.generatorDelta]])
              (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))
                ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                  :: [SldCell.wire, SldCell.generatorMu] :: [SldCell.generatorMu] :: []))
            = [SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers
                  (sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                    [[SldCell.wire, SldCell.wire, SldCell.generatorDelta]])
                  (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))
                    ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                      :: [SldCell.wire, SldCell.generatorMu]
                      :: [SldCell.generatorMu] :: [])) from rfl,
          sldAppendLayersAssoc] at prefixed
        exact prefixed
      have freshCopySlides : SldAreConvertibleLayers 2
          ([SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList scaleFactorPred))
                ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
                  :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))
                      ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                        :: [SldCell.wire, SldCell.generatorMu]
                        :: [SldCell.generatorMu] :: [])))
          ([SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 3 (lstScaleLayerList scaleFactorPred))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.generatorMu]
                    :: [SldCell.generatorMu] :: []))) := by
        have slideInstance := sldLowerLayerSlidesDownPastBlock
          [SldCell.wire, SldCell.generatorDelta] (lstScaleLayerList scaleFactorPred) 1
          (lstScaleLayersAreComposable scaleFactorPred)
          (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactorPred))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorMu] :: [SldCell.generatorMu] :: []))
        rw [lstScaleLayersReach] at slideInstance
        exact SldAreConvertibleLayers.underLayerPrefix 2
          [SldCell.generatorDelta, SldCell.wire]
          (SldAreConvertibleLayers.fromSymmetry slideInstance)
      exact SldAreConvertibleLayers.fromTransitivity bimonoidFires
        (SldAreConvertibleLayers.fromTransitivity doubleAddSplits
          (SldAreConvertibleLayers.fromTransitivity deepAddSlides
            (SldAreConvertibleLayers.fromTransitivity recursionUnderPrefix
              (SldAreConvertibleLayers.fromTransitivity doubleCopySplits
                (SldAreConvertibleLayers.fromTransitivity midSwapSlides
                  (SldAreConvertibleLayers.fromTransitivity swapConvertsUnderPrefix
                    (SldAreConvertibleLayers.fromTransitivity swapDiesInTree
                      (SldAreConvertibleLayers.fromSymmetry
                        (SldAreConvertibleLayers.fromTransitivity addCopyExchange
                          (SldAreConvertibleLayers.fromTransitivity addSlideUnderPrefix
                            freshCopySlides))))))))))



/-! ## The five-strand merge-route kit (for the gadget-level mu interaction) -/

/-- A crossing feeding the lower add re-routes: `(w | tau) ; (mu | w) ~
(tau | w) ; (w | mu) ; tau`. -/
theorem lcoSwapThenUpperAddReroutes (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire] :: suffixLayers)
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu] :: [SldCell.crossing] :: suffixLayers) := by
  have tauPairMaterializes : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire] :: suffixLayers)
      ([SldCell.crossing, SldCell.wire] :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire] :: suffixLayers) :=
    SldAreConvertibleLayers.fromSymmetry
      (SldAreConvertibleLayers.fromSwapInvolutionRow 0 1
        ([SldCell.wire, SldCell.crossing]
          :: [SldCell.generatorMu, SldCell.wire] :: suffixLayers))
  have addSlides : SldAreConvertibleLayers 3
      ([SldCell.crossing, SldCell.wire] :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire] :: suffixLayers)
      ([SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers) :=
    SldAreConvertibleLayers.underLayerPrefix 3 [SldCell.crossing, SldCell.wire]
      (lcoAddSlidesBelowParkedStrand suffixLayers)
  exact SldAreConvertibleLayers.fromTransitivity tauPairMaterializes addSlides

/-- THE FIVE-STRAND MERGE-ROUTE ALIGNMENT: the two-gadget spine of the distributed add
(`route the accumulator down, add twice, climb`) converts to the single-spine route
(`cross the summand copies, add pairwise, add once`).  Pure crossing/add material at
boundary five — Nmu, the mirror-Nmu kit, one involution, two exchanges, one
associativity. -/
theorem lcoFiveStrandMergeRoutesAgree (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire] :: suffixLayers)
      ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu, SldCell.wire]
        :: [SldCell.crossing] :: suffixLayers) := by
  have headNmuRefolds : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire] :: suffixLayers)
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire] :: suffixLayers) :=
    SldAreConvertibleLayers.fromSymmetry
      (SldAreConvertibleLayers.fromSwapPastAddRow 0 2
        ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
          :: [SldCell.wire, SldCell.crossing]
          :: [SldCell.generatorMu, SldCell.wire] :: suffixLayers))
  have tailReroutes : SldAreConvertibleLayers 5
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire] :: suffixLayers)
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers) :=
    sldConvUnderPrefixList
      [[SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire],
        [SldCell.crossing, SldCell.wire, SldCell.wire],
        [SldCell.wire, SldCell.generatorMu, SldCell.wire]] 5 _ _
      (lcoSwapThenUpperAddReroutes suffixLayers)
  have midKitExpands : SldAreConvertibleLayers 5
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers)
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers) := by
    have belowPaddedKit := sldConvPadsBelow (lcoAddSlidesBelowParkedStrand []) 1
    have kitWithSuffix := sldConvAppendsSuffix belowPaddedKit
      ([SldCell.wire, SldCell.generatorMu] :: [SldCell.crossing] :: suffixLayers)
    exact sldConvUnderPrefixList
      [[SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire],
        [SldCell.crossing, SldCell.wire, SldCell.wire]] 5 _ _
      (SldAreConvertibleLayers.fromSymmetry kitWithSuffix)
  have tauPairDies : SldAreConvertibleLayers 5
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers)
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers) :=
    SldAreConvertibleLayers.underLayerPrefix 5
      [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
      (SldAreConvertibleLayers.fromSwapInvolutionRow 0 2
        ([SldCell.wire, SldCell.crossing, SldCell.wire]
          :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: [SldCell.wire, SldCell.generatorMu]
          :: [SldCell.crossing] :: suffixLayers))
  have addSwapExchange : SldAreConvertibleLayers 5
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers)
      ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers) :=
    sldDisjointLayersExchange [SldCell.generatorMu] [SldCell.crossing, SldCell.wire]
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers)
  have assocFires : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers)
      ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers) :=
    SldAreConvertibleLayers.underLayerPrefix 5
      [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
      (SldAreConvertibleLayers.fromAddAssociativityRow 0 2
        ([SldCell.wire, SldCell.generatorMu] :: [SldCell.crossing] :: suffixLayers))
  have addsExchange : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu]
        :: [SldCell.crossing] :: suffixLayers)
      ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu, SldCell.wire]
        :: [SldCell.crossing] :: suffixLayers) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire],
        [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]] 5 _ _
      (sldDisjointLayersExchange [SldCell.generatorMu] [SldCell.generatorMu]
        ([SldCell.crossing] :: suffixLayers))
  exact SldAreConvertibleLayers.fromTransitivity headNmuRefolds
    (SldAreConvertibleLayers.fromTransitivity tailReroutes
      (SldAreConvertibleLayers.fromTransitivity midKitExpands
        (SldAreConvertibleLayers.fromTransitivity tauPairDies
          (SldAreConvertibleLayers.fromTransitivity addSwapExchange
            (SldAreConvertibleLayers.fromTransitivity assocFires addsExchange)))))


/-! ## GADGET-MU: the merge gadget distributes over a summed source -/

/-- Left spine of the gadget distributivity: open the bimonoid square, split, slide, fire
the padded SCALE-MU, split the copies, migrate the emitted crossing through the towers. -/
theorem lcoGadgetMuLeftSpine (scaleFactor : Nat) :
    SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorMu]
        :: [SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu, SldCell.wire]
                :: [SldCell.crossing] :: []))) := by
  have aboveReach : sldLayersTargetArityFrom 2
      (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor)) = 2 := by
    have liftedReach := sldPadLayersAboveTargetArityFrom 1 (lstScaleLayerList scaleFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have bimonoidFires : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorMu]
        :: [SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.generatorMu]
        :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [])) :=
    SldAreConvertibleLayers.fromBimonoidSquareRow 1 0
      (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
        ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))
  have doubleAddSplits : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.generatorMu]
        :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
        :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [])) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.generatorDelta, SldCell.generatorDelta],
        [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]] 3 _ _
      (SldAreConvertibleLayers.layerSplitTopActsFirst [SldCell.wire, SldCell.generatorMu]
        [SldCell.generatorMu]
        (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
          ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [])))
  have deepAddSlides : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
        :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.wire, SldCell.generatorMu]
              :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [])) := by
    have slideInstance := sldLowerLayerSlidesDownPastBlock [SldCell.generatorMu]
      (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor)) 2
      (sldPadLayersAboveAreComposableFrom 1 (lstScaleLayerList scaleFactor) 1
        (lstScaleLayersAreComposable scaleFactor))
      ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [])
    rw [aboveReach, lstPadBelowOfPadAboveIsPadWindow,
      lstPadBelowOfPadAboveIsPadWindow] at slideInstance
    exact sldConvUnderPrefixList
      [[SldCell.wire, SldCell.generatorDelta, SldCell.generatorDelta],
        [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire],
        [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]] 3 _ _ slideInstance
  have scaleMuAtWindow : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.wire, SldCell.generatorMu]
              :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))
      (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
        (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList scaleFactor))
          ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
            :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))) := by
    have windowPadded := lcoConvPadsWindow
      (lcoScaleTowerDistributesOverAdd scaleFactor) 1 2
    rw [show sldPadWindow 1 2
          ([SldCell.generatorMu] :: lstScaleLayerList scaleFactor)
        = [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: sldPadWindow 1 2 (lstScaleLayerList scaleFactor) from rfl,
      lcoPadWindowOfAppendLayers, lcoPadWindowOfAppendLayers,
      lcoPadWindowOfPadLayersBelow, lcoPadWindowOfPadLayersAbove] at windowPadded
    have withSuffix := sldConvAppendsSuffix windowPadded
      ([SldCell.wire, SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [])
    rw [sldAppendLayersAssoc, sldAppendLayersAssoc] at withSuffix
    exact withSuffix
  have recursionUnderPrefix : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.wire, SldCell.generatorMu]
              :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList scaleFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.generatorDelta, SldCell.generatorDelta],
        [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]] 3 _ _ scaleMuAtWindow
  have doubleCopySplits : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList scaleFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList scaleFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))) :=
    SldAreConvertibleLayers.layerSplitTopActsFirst [SldCell.wire, SldCell.generatorDelta]
      [SldCell.generatorDelta]
      ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList scaleFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [])))
  have tauSlidesPastFirstTower : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList scaleFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
                    :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))) := by
    have slideInstance := sldLowerLayerSlidesDownPastBlock
      [SldCell.crossing, SldCell.wire]
      (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor)) 2
      (sldPadLayersAboveAreComposableFrom 1 (lstScaleLayerList scaleFactor) 1
        (lstScaleLayersAreComposable scaleFactor))
      (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList scaleFactor))
        ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
          :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))
    rw [aboveReach, lstPadBelowOfPadAboveIsPadWindow,
      lstPadBelowOfPadAboveIsPadWindow] at slideInstance
    exact sldConvUnderPrefixList
      [[SldCell.wire, SldCell.generatorDelta, SldCell.wire],
        [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]] 3 _ _
      slideInstance
  have scaleTauMirrorAtWindow : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
              :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))
      (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
        ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
          :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
          :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [])) := by
    have windowPadded := lcoConvPadsWindow (lcoSwapDescendsIntoScaleTower scaleFactor) 2 1
    rw [show sldPadWindow 2 1
          ([SldCell.crossing] :: sldPadLayersBelow 1 (lstScaleLayerList scaleFactor))
        = [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
          :: sldPadWindow 2 1 (sldPadLayersBelow 1 (lstScaleLayerList scaleFactor))
        from rfl,
      lcoPadWindowOfPadLayersBelow, lcoPadWindowOfAppendLayers,
      lcoPadWindowOfPadLayersAbove] at windowPadded
    have withSuffix := sldConvAppendsSuffix windowPadded
      ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
        :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [])
    rw [sldAppendLayersAssoc] at withSuffix
    exact withSuffix
  have mirrorUnderPrefix : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
                    :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))) := by
    have prefixReach : sldLayersTargetArityFrom 3
        ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldPadWindow 1 3 (lstScaleLayerList scaleFactor)) = 5 := by
      show sldLayersTargetArityFrom 5
        (sldPadWindow 1 3 (lstScaleLayerList scaleFactor)) = 5
      have liftedReach := sldPadWindowTargetArityFrom 1 3 (lstScaleLayerList scaleFactor) 1
      rw [lstScaleLayersReach] at liftedReach
      exact liftedReach
    refine sldConvUnderPrefixList
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldPadWindow 1 3 (lstScaleLayerList scaleFactor)) 3 _ _ ?_
    rw [prefixReach]
    exact scaleTauMirrorAtWindow
  exact SldAreConvertibleLayers.fromTransitivity bimonoidFires
    (SldAreConvertibleLayers.fromTransitivity doubleAddSplits
      (SldAreConvertibleLayers.fromTransitivity deepAddSlides
        (SldAreConvertibleLayers.fromTransitivity recursionUnderPrefix
          (SldAreConvertibleLayers.fromTransitivity doubleCopySplits
            (SldAreConvertibleLayers.fromTransitivity tauSlidesPastFirstTower
              mirrorUnderPrefix)))))


/-- Right spine of the gadget distributivity: exchange the emitted crossing and second copy
out of the first gadget, migrate the first add and the crossing pair below the second tower,
landing on the five-strand spine. -/
theorem lcoGadgetMuRightSpine (scaleFactor : Nat) :
    SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.generatorMu, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
              ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
                :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing]
                :: [SldCell.generatorMu, SldCell.wire] :: []))) := by
  have belowReach : sldLayersTargetArityFrom 2
      (sldPadLayersBelow 1 (lstScaleLayerList scaleFactor)) = 2 := by
    have liftedReach := sldPadLayersBelowTargetArityFrom 1 (lstScaleLayerList scaleFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have windowReachOneTwo : sldLayersTargetArityFrom 4
      (sldPadWindow 1 2 (lstScaleLayerList scaleFactor)) = 4 := by
    have liftedReach := sldPadWindowTargetArityFrom 1 2 (lstScaleLayerList scaleFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have windowReachOneOne : sldLayersTargetArityFrom 3
      (sldPadWindow 1 1 (lstScaleLayerList scaleFactor)) = 3 := by
    have liftedReach := sldPadWindowTargetArityFrom 1 1 (lstScaleLayerList scaleFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have windowReachOneThree : sldLayersTargetArityFrom 5
      (sldPadWindow 1 3 (lstScaleLayerList scaleFactor)) = 5 := by
    have liftedReach := sldPadWindowTargetArityFrom 1 3 (lstScaleLayerList scaleFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have tauCopyExchange : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.generatorMu, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: [SldCell.crossing, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.generatorMu, SldCell.wire] :: []))) := by
    have prefixReach : sldLayersTargetArityFrom 3
        ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
              [[SldCell.generatorMu, SldCell.wire, SldCell.wire]]) = 3 := by
      show sldLayersTargetArityFrom 4
        (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
          [[SldCell.generatorMu, SldCell.wire, SldCell.wire]]) = 3
      rw [sldAppendLayersTargetArityFrom, windowReachOneTwo]
      rfl
    have core : SldAreConvertibleLayers 3
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
                [[SldCell.generatorMu, SldCell.wire, SldCell.wire]])
          ([SldCell.crossing, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                  :: [SldCell.wire, SldCell.crossing]
                  :: [SldCell.generatorMu, SldCell.wire] :: [])))
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
                [[SldCell.generatorMu, SldCell.wire, SldCell.wire]])
          ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: [SldCell.crossing, SldCell.wire, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                  :: [SldCell.wire, SldCell.crossing]
                  :: [SldCell.generatorMu, SldCell.wire] :: []))) := by
      refine sldConvUnderPrefixList
        ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
              [[SldCell.generatorMu, SldCell.wire, SldCell.wire]]) 3 _ _ ?_
      rw [prefixReach]
      exact sldDisjointLayersExchange [SldCell.crossing] [SldCell.generatorDelta]
        (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
          ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing]
            :: [SldCell.generatorMu, SldCell.wire] :: []))
    rw [show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
                [[SldCell.generatorMu, SldCell.wire, SldCell.wire]])
          ([SldCell.crossing, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                  :: [SldCell.wire, SldCell.crossing]
                  :: [SldCell.generatorMu, SldCell.wire] :: []))
        = [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
                [[SldCell.generatorMu, SldCell.wire, SldCell.wire]])
              ([SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
                :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                    ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                      :: [SldCell.wire, SldCell.crossing]
                      :: [SldCell.generatorMu, SldCell.wire] :: [])) from rfl,
      sldAppendLayersAssoc,
      show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
                [[SldCell.generatorMu, SldCell.wire, SldCell.wire]])
          ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: [SldCell.crossing, SldCell.wire, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                  :: [SldCell.wire, SldCell.crossing]
                  :: [SldCell.generatorMu, SldCell.wire] :: []))
        = [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
                [[SldCell.generatorMu, SldCell.wire, SldCell.wire]])
              ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
                :: [SldCell.crossing, SldCell.wire, SldCell.wire]
                :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                    ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                      :: [SldCell.wire, SldCell.crossing]
                      :: [SldCell.generatorMu, SldCell.wire] :: [])) from rfl,
      sldAppendLayersAssoc] at core
    exact core
  have addCopyExchange : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: [SldCell.crossing, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.generatorMu, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.generatorMu, SldCell.wire] :: []))) := by
    have prefixReach : sldLayersTargetArityFrom 3
        ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldPadWindow 1 2 (lstScaleLayerList scaleFactor)) = 4 := by
      show sldLayersTargetArityFrom 4
        (sldPadWindow 1 2 (lstScaleLayerList scaleFactor)) = 4
      exact windowReachOneTwo
    refine sldConvUnderPrefixList
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldPadWindow 1 2 (lstScaleLayerList scaleFactor)) 3 _ _ ?_
    rw [prefixReach]
    exact sldDisjointLayersExchange [SldCell.generatorMu]
      [SldCell.wire, SldCell.generatorDelta]
      ([SldCell.crossing, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire] :: []))
  have freshCopySlides : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.generatorMu, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.generatorMu, SldCell.wire] :: []))) := by
    have slideInstance := sldLowerLayerSlidesDownPastBlock [SldCell.generatorDelta]
      (sldPadWindow 1 1 (lstScaleLayerList scaleFactor)) 3
      (sldPadWindowIsComposableFrom 1 1 (lstScaleLayerList scaleFactor) 1
        (lstScaleLayersAreComposable scaleFactor))
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire] :: []))
    rw [windowReachOneOne, sldPadLayersBelowOfPadWindow,
      sldPadLayersBelowOfPadWindow] at slideInstance
    exact SldAreConvertibleLayers.underLayerPrefix 3
      [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
      (SldAreConvertibleLayers.fromSymmetry slideInstance)
  have nmuFires : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.generatorMu, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.generatorMu, SldCell.wire] :: []))) := by
    have prefixReach : sldLayersTargetArityFrom 3
        ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldPadWindow 1 3 (lstScaleLayerList scaleFactor)) = 5 := by
      show sldLayersTargetArityFrom 5
        (sldPadWindow 1 3 (lstScaleLayerList scaleFactor)) = 5
      exact windowReachOneThree
    refine sldConvUnderPrefixList
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldPadWindow 1 3 (lstScaleLayerList scaleFactor)) 3 _ _ ?_
    rw [prefixReach]
    exact SldAreConvertibleLayers.fromSwapPastAddRow 0 2
      (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
        ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
          :: [SldCell.wire, SldCell.crossing]
          :: [SldCell.generatorMu, SldCell.wire] :: []))
  have secondAddSlides : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire] :: []))
      (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
        ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
          :: [SldCell.wire, SldCell.crossing]
          :: [SldCell.generatorMu, SldCell.wire] :: [])) := by
    have slideInstance := sldUpperLayerSlidesDownPastBlock [SldCell.wire, SldCell.generatorMu]
      (sldPadLayersBelow 1 (lstScaleLayerList scaleFactor)) 2
      (sldPadLayersBelowAreComposableFrom 1 (lstScaleLayerList scaleFactor) 1
        (lstScaleLayersAreComposable scaleFactor))
      ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire] :: [])
    rw [belowReach, lstPadAboveOfPadBelowIsPadWindow,
      lstPadAboveOfPadBelowIsPadWindow] at slideInstance
    exact slideInstance
  have secondAddUnderPrefix : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.generatorMu, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.generatorMu, SldCell.wire] :: []))) := by
    have prefixReach : sldLayersTargetArityFrom 3
        ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
              [[SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire],
                [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]]) = 5 := by
      show sldLayersTargetArityFrom 5
        (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
          [[SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire],
            [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]]) = 5
      rw [sldAppendLayersTargetArityFrom, windowReachOneThree]
      rfl
    have core : SldAreConvertibleLayers 3
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
                [[SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire],
                  [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]])
          ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                  :: [SldCell.wire, SldCell.crossing]
                  :: [SldCell.generatorMu, SldCell.wire] :: [])))
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
                [[SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire],
                  [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]])
          (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire] :: []))) := by
      refine sldConvUnderPrefixList
        ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
              [[SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire],
                [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]]) 3 _ _ ?_
      rw [prefixReach]
      exact secondAddSlides
    rw [show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
                [[SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire],
                  [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]])
          ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                  :: [SldCell.wire, SldCell.crossing]
                  :: [SldCell.generatorMu, SldCell.wire] :: []))
        = [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
                [[SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire],
                  [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]])
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                    ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                      :: [SldCell.wire, SldCell.crossing]
                      :: [SldCell.generatorMu, SldCell.wire] :: [])) from rfl,
      sldAppendLayersAssoc,
      show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
                [[SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire],
                  [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]])
          (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire] :: []))
        = [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
                [[SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire],
                  [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]])
              (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
                ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                  :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
                  :: [SldCell.wire, SldCell.crossing]
                  :: [SldCell.generatorMu, SldCell.wire] :: [])) from rfl,
      sldAppendLayersAssoc] at core
    exact core
  have tauPairSlides : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.generatorMu, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
              ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
                :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing]
                :: [SldCell.generatorMu, SldCell.wire] :: []))) := by
    have lowTauSlides : SldAreConvertibleLayers 5
        ([SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
          :: sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing]
                :: [SldCell.generatorMu, SldCell.wire] :: []))
        (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
          ([SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing]
            :: [SldCell.generatorMu, SldCell.wire] :: [])) := by
      have slideInstance := sldUpperLayerSlidesDownPastBlock [SldCell.crossing]
        (sldPadWindow 1 1 (lstScaleLayerList scaleFactor)) 3
        (sldPadWindowIsComposableFrom 1 1 (lstScaleLayerList scaleFactor) 1
          (lstScaleLayersAreComposable scaleFactor))
        ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
          :: [SldCell.wire, SldCell.crossing]
          :: [SldCell.generatorMu, SldCell.wire] :: [])
      rw [windowReachOneOne, sldPadLayersAboveOfPadWindow,
        sldPadLayersAboveOfPadWindow] at slideInstance
      exact slideInstance
    have highTauSlides : SldAreConvertibleLayers 5
        ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
          :: sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
              ([SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing]
                :: [SldCell.generatorMu, SldCell.wire] :: []))
        (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
          ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
            :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing]
            :: [SldCell.generatorMu, SldCell.wire] :: [])) := by
      have slideInstance := sldUpperLayerSlidesDownPastBlock
        [SldCell.wire, SldCell.crossing]
        (sldPadLayersBelow 1 (lstScaleLayerList scaleFactor)) 2
        (sldPadLayersBelowAreComposableFrom 1 (lstScaleLayerList scaleFactor) 1
          (lstScaleLayersAreComposable scaleFactor))
        ([SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
          :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
          :: [SldCell.wire, SldCell.crossing]
          :: [SldCell.generatorMu, SldCell.wire] :: [])
      rw [belowReach, lstPadAboveOfPadBelowIsPadWindow,
        lstPadAboveOfPadBelowIsPadWindow] at slideInstance
      exact slideInstance
    have prefixReach : sldLayersTargetArityFrom 3
        ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldPadWindow 1 3 (lstScaleLayerList scaleFactor)) = 5 := by
      show sldLayersTargetArityFrom 5
        (sldPadWindow 1 3 (lstScaleLayerList scaleFactor)) = 5
      exact windowReachOneThree
    refine sldConvUnderPrefixList
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldPadWindow 1 3 (lstScaleLayerList scaleFactor)) 3 _ _ ?_
    rw [prefixReach]
    refine SldAreConvertibleLayers.fromTransitivity ?_ highTauSlides
    exact SldAreConvertibleLayers.underLayerPrefix 5
      [SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire] lowTauSlides
  exact SldAreConvertibleLayers.fromTransitivity tauCopyExchange
    (SldAreConvertibleLayers.fromTransitivity addCopyExchange
      (SldAreConvertibleLayers.fromTransitivity freshCopySlides
        (SldAreConvertibleLayers.fromTransitivity nmuFires
          (SldAreConvertibleLayers.fromTransitivity secondAddUnderPrefix tauPairSlides))))


/-- GADGET-MU: the merge gadget absorbs a summed source — `(wire | mu) ; gadget(s) ~
(gadget(s) | wire) ; (wire | gadget(s)) ; (mu | wire)` (the derivation
`(u, x + y) -> (x + y, u + s*(x+y))` factored through merging x then y).  The left spine
opens the bimonoid square and fires the padded SCALE-MU; the right spine unfolds the two
gadget copies; the five-strand alignment meets them in the middle. -/
theorem lcoGadgetDistributesOverAdd (scaleFactor : Nat) :
    SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorMu] :: lstGadgetLayerList scaleFactor)
      (sldAppendLayers (sldPadLayersBelow 1 (lstGadgetLayerList scaleFactor))
        (sldAppendLayers (sldPadLayersAbove 1 (lstGadgetLayerList scaleFactor))
          [[SldCell.generatorMu, SldCell.wire]])) := by
  have windowReachOneThree : sldLayersTargetArityFrom 5
      (sldPadWindow 1 3 (lstScaleLayerList scaleFactor)) = 5 := by
    have liftedReach := sldPadWindowTargetArityFrom 1 3 (lstScaleLayerList scaleFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have windowReachThreeOne : sldLayersTargetArityFrom 5
      (sldPadWindow 3 1 (lstScaleLayerList scaleFactor)) = 5 := by
    have liftedReach := sldPadWindowTargetArityFrom 3 1 (lstScaleLayerList scaleFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have padBelowShape : sldPadLayersBelow 1
      (sldAppendLayers [[SldCell.wire, SldCell.generatorDelta]]
        (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
          [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]))
      = [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire] :: []) := by
    rw [sldPadLayersBelowOfAppend, sldPadLayersBelowOfAppend,
      sldPadLayersBelowOfPadWindow]
    rfl
  have padAboveShape : sldPadLayersAbove 1
      (sldAppendLayers [[SldCell.wire, SldCell.generatorDelta]]
        (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
          [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]))
      = [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: []) := by
    rw [sldPadLayersAboveOfAppend, sldPadLayersAboveOfAppend,
      sldPadLayersAboveOfPadWindow]
    rfl
  have fiveStrandPrefixed : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
              ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
                :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing]
                :: [SldCell.generatorMu, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu, SldCell.wire]
                :: [SldCell.crossing] :: []))) := by
    have prefixReach : sldLayersTargetArityFrom 3
        ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
              (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))) = 5 := by
      show sldLayersTargetArityFrom 5
        (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
          (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))) = 5
      rw [sldAppendLayersTargetArityFrom, windowReachOneThree]
      exact windowReachThreeOne
    have core : SldAreConvertibleLayers 3
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
                (sldPadWindow 3 1 (lstScaleLayerList scaleFactor)))
          ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
            :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing]
            :: [SldCell.generatorMu, SldCell.wire] :: []))
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
                (sldPadWindow 3 1 (lstScaleLayerList scaleFactor)))
          ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
            :: [SldCell.generatorMu, SldCell.wire]
            :: [SldCell.crossing] :: [])) := by
      refine sldConvUnderPrefixList
        ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
              (sldPadWindow 3 1 (lstScaleLayerList scaleFactor))) 3 _ _ ?_
      rw [prefixReach]
      exact lcoFiveStrandMergeRoutesAgree []
    rw [show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
                (sldPadWindow 3 1 (lstScaleLayerList scaleFactor)))
          ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
            :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing]
            :: [SldCell.generatorMu, SldCell.wire] :: [])
        = [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
                (sldPadWindow 3 1 (lstScaleLayerList scaleFactor)))
              ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
                :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing]
                :: [SldCell.generatorMu, SldCell.wire] :: []) from rfl,
      sldAppendLayersAssoc,
      show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
                (sldPadWindow 3 1 (lstScaleLayerList scaleFactor)))
          ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
            :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
            :: [SldCell.generatorMu, SldCell.wire]
            :: [SldCell.crossing] :: [])
        = [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList scaleFactor))
                (sldPadWindow 3 1 (lstScaleLayerList scaleFactor)))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu, SldCell.wire]
                :: [SldCell.crossing] :: []) from rfl,
      sldAppendLayersAssoc] at core
    exact core
  rw [lstGadgetLayerShape scaleFactor, padBelowShape, padAboveShape]
  show SldAreConvertibleLayers 3
    ([SldCell.wire, SldCell.generatorMu]
      :: [SldCell.wire, SldCell.generatorDelta]
      :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
          ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: []))
    ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
      :: sldAppendLayers
          (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire] :: []))
          ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: []))
                ([SldCell.generatorMu, SldCell.wire] :: [])))
  rw [sldAppendLayersAssoc (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire] :: []),
    sldAppendLayersAssoc (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
      ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: [])
      ([SldCell.generatorMu, SldCell.wire] :: [])]
  exact SldAreConvertibleLayers.fromTransitivity (lcoGadgetMuLeftSpine scaleFactor)
    (SldAreConvertibleLayers.fromSymmetry
      (SldAreConvertibleLayers.fromTransitivity (lcoGadgetMuRightSpine scaleFactor)
        fiveStrandPrefixed))


/-! ## THE MU CORE: fan duplication -/

/-- THE MU BOTTOM CORE: the fan duplicates an added source —
`(wires(t) | mu) ; fan(t, col) ~ (fan(t, col) | wire) ; fan(t, col)` (the derivation
`acc_i + col_i * (x + y) = (acc_i + col_i * x) + col_i * y`).  Source-climb induction: the
base is B3 plus one split; each rung fires the padded GADGET-MU, the below-padded induction
hypothesis, and the Godement block slide between the fresh gadget and the shorter fan. -/
theorem lcoMuFanDuplication : (vectorLength : Nat) -> (columnEntries : Nat -> Nat) ->
    SldAreConvertibleLayers (vectorLength + 2)
      (sldAppendCells (sldWireLayerOfArity vectorLength) [SldCell.generatorMu]
        :: lstFanLayerList vectorLength columnEntries)
      (sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList vectorLength columnEntries))
        (lstFanLayerList vectorLength columnEntries))
  | 0, columnEntries => by
      rw [lstFanZeroLayerShape]
      have discardSplits : SldAreConvertibleLayers 2
          ([SldCell.generatorMu] :: [SldCell.generatorEpsilon] :: [])
          ([SldCell.generatorEpsilon, SldCell.generatorEpsilon] :: []) :=
        SldAreConvertibleLayers.fromDiscardAfterAddRow 0 0 []
      have discardPairSplits : SldAreConvertibleLayers 2
          ([SldCell.generatorEpsilon, SldCell.generatorEpsilon] :: [])
          ([SldCell.generatorEpsilon, SldCell.wire] :: [SldCell.generatorEpsilon] :: []) :=
        SldAreConvertibleLayers.layerSplitTopActsFirst [SldCell.generatorEpsilon]
          [SldCell.generatorEpsilon] []
      exact SldAreConvertibleLayers.fromTransitivity discardSplits discardPairSplits
  | vectorLengthPred + 1, columnEntries => by
      rw [lstFanSuccUnfolds vectorLengthPred columnEntries]
      have firstLayerEq : sldAppendCells (sldWireLayerOfArity (vectorLengthPred + 1))
          [SldCell.generatorMu]
          = sldAppendCells (sldWireLayerOfArity vectorLengthPred)
              [SldCell.wire, SldCell.generatorMu] := by
        rw [(sldWireLayerSplitsAtCount vectorLengthPred 1).symm, sldAppendCellsAssoc]
        exact rfl
      rw [firstLayerEq]
      have targetShape : sldAppendLayers
          (sldPadLayersBelow 1
            (sldAppendLayers
              (sldPadLayersAbove vectorLengthPred
                (lstGadgetLayerList (columnEntries vectorLengthPred)))
              (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred columnEntries))))
          (sldAppendLayers
            (sldPadLayersAbove vectorLengthPred
              (lstGadgetLayerList (columnEntries vectorLengthPred)))
            (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred columnEntries)))
          = sldAppendLayers
              (sldPadWindow vectorLengthPred 1
                (lstGadgetLayerList (columnEntries vectorLengthPred)))
              (sldAppendLayers
                (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred columnEntries))
                (sldAppendLayers
                  (sldPadLayersAbove vectorLengthPred
                    (lstGadgetLayerList (columnEntries vectorLengthPred)))
                  (sldPadLayersBelow 1
                    (lstFanLayerList vectorLengthPred columnEntries)))) := by
        rw [sldPadLayersBelowOfAppend, lstPadLayersBelowCompose,
          lstPadBelowOfPadAboveIsPadWindow, sldAppendLayersAssoc]
      rw [targetShape]
      have gadgetReach : sldLayersTargetArityFrom 2
          (lstGadgetLayerList (columnEntries vectorLengthPred)) = 2 :=
        lstGadgetLayersReach (columnEntries vectorLengthPred)
      have walkWindow : sldLayersTargetArityFrom (vectorLengthPred + 1 + 2)
          (sldPadWindow vectorLengthPred 1
            (lstGadgetLayerList (columnEntries vectorLengthPred)))
          = vectorLengthPred + 3 := by
        have liftedReach := sldPadWindowTargetArityFrom vectorLengthPred 1
          (lstGadgetLayerList (columnEntries vectorLengthPred)) 2
        rw [gadgetReach] at liftedReach
        exact liftedReach
      have walkAbove : sldLayersTargetArityFrom (vectorLengthPred + 3)
          (sldPadLayersAbove (vectorLengthPred + 1)
            (lstGadgetLayerList (columnEntries vectorLengthPred)))
          = vectorLengthPred + 3 := by
        have liftedReach := sldPadLayersAboveTargetArityFrom (vectorLengthPred + 1)
          (lstGadgetLayerList (columnEntries vectorLengthPred)) 2
        rw [gadgetReach] at liftedReach
        exact liftedReach
      have gadgetMuWithSuffix : SldAreConvertibleLayers (vectorLengthPred + 1 + 2)
          (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
              [SldCell.wire, SldCell.generatorMu]
            :: sldAppendLayers
                (sldPadLayersAbove vectorLengthPred
                  (lstGadgetLayerList (columnEntries vectorLengthPred)))
                (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred columnEntries)))
          (sldAppendLayers
            (sldPadWindow vectorLengthPred 1
              (lstGadgetLayerList (columnEntries vectorLengthPred)))
            (sldAppendLayers
              (sldPadLayersAbove (vectorLengthPred + 1)
                (lstGadgetLayerList (columnEntries vectorLengthPred)))
              (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                  [SldCell.generatorMu, SldCell.wire]
                :: sldPadLayersBelow 1
                    (lstFanLayerList vectorLengthPred columnEntries)))) := by
        have paddedGadgetMu := sldConvPadsAbove
          (lcoGadgetDistributesOverAdd (columnEntries vectorLengthPred)) vectorLengthPred
        rw [sldPadLayersAboveOfAppend, sldPadLayersAboveOfAppend,
          lstPadAboveOfPadBelowIsPadWindow, lstPadLayersAboveCompose] at paddedGadgetMu
        have withSuffix := sldConvAppendsSuffix paddedGadgetMu
          (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred columnEntries))
        rw [sldAppendLayersAssoc, sldAppendLayersAssoc] at withSuffix
        exact withSuffix
      have recursionAfterGadgets : SldAreConvertibleLayers (vectorLengthPred + 1 + 2)
          (sldAppendLayers
            (sldPadWindow vectorLengthPred 1
              (lstGadgetLayerList (columnEntries vectorLengthPred)))
            (sldAppendLayers
              (sldPadLayersAbove (vectorLengthPred + 1)
                (lstGadgetLayerList (columnEntries vectorLengthPred)))
              (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                  [SldCell.generatorMu, SldCell.wire]
                :: sldPadLayersBelow 1
                    (lstFanLayerList vectorLengthPred columnEntries))))
          (sldAppendLayers
            (sldPadWindow vectorLengthPred 1
              (lstGadgetLayerList (columnEntries vectorLengthPred)))
            (sldAppendLayers
              (sldPadLayersAbove (vectorLengthPred + 1)
                (lstGadgetLayerList (columnEntries vectorLengthPred)))
              (sldAppendLayers
                (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred columnEntries))
                (sldPadLayersBelow 1
                  (lstFanLayerList vectorLengthPred columnEntries))))) := by
        have paddedRecursion := sldConvPadsBelow
          (lcoMuFanDuplication vectorLengthPred columnEntries) 1
        rw [sldPadLayersBelowOfAppend, lstPadLayersBelowCompose,
          show sldPadLayersBelow 1
              (sldAppendCells (sldWireLayerOfArity vectorLengthPred) [SldCell.generatorMu]
                :: lstFanLayerList vectorLengthPred columnEntries)
            = sldAppendCells
                (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                  [SldCell.generatorMu])
                (sldWireLayerOfArity 1)
              :: sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred columnEntries)
            from rfl,
          sldAppendCellsAssoc] at paddedRecursion
        refine sldConvUnderPrefixList
          (sldPadWindow vectorLengthPred 1
            (lstGadgetLayerList (columnEntries vectorLengthPred)))
          (vectorLengthPred + 1 + 2) _ _ ?_
        rw [walkWindow]
        refine sldConvUnderPrefixList
          (sldPadLayersAbove (vectorLengthPred + 1)
            (lstGadgetLayerList (columnEntries vectorLengthPred)))
          (vectorLengthPred + 3) _ _ ?_
        rw [walkAbove]
        exact paddedRecursion
      have blockSlideBack : SldAreConvertibleLayers (vectorLengthPred + 1 + 2)
          (sldAppendLayers
            (sldPadWindow vectorLengthPred 1
              (lstGadgetLayerList (columnEntries vectorLengthPred)))
            (sldAppendLayers
              (sldPadLayersAbove (vectorLengthPred + 1)
                (lstGadgetLayerList (columnEntries vectorLengthPred)))
              (sldAppendLayers
                (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred columnEntries))
                (sldPadLayersBelow 1
                  (lstFanLayerList vectorLengthPred columnEntries)))))
          (sldAppendLayers
            (sldPadWindow vectorLengthPred 1
              (lstGadgetLayerList (columnEntries vectorLengthPred)))
            (sldAppendLayers
              (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred columnEntries))
              (sldAppendLayers
                (sldPadLayersAbove vectorLengthPred
                  (lstGadgetLayerList (columnEntries vectorLengthPred)))
                (sldPadLayersBelow 1
                  (lstFanLayerList vectorLengthPred columnEntries))))) := by
        have slideInstance := sldBlockSlidesDownPastBlock
          (lstFanLayerList vectorLengthPred columnEntries) (vectorLengthPred + 1)
          (lstFanLayersAreComposable vectorLengthPred columnEntries)
          (lstGadgetLayerList (columnEntries vectorLengthPred)) 2
          (lstGadgetLayersAreComposable (columnEntries vectorLengthPred))
          (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred columnEntries))
        rw [lstFanLayersReach, lstGadgetLayersReach] at slideInstance
        refine sldConvUnderPrefixList
          (sldPadWindow vectorLengthPred 1
            (lstGadgetLayerList (columnEntries vectorLengthPred)))
          (vectorLengthPred + 1 + 2) _ _ ?_
        rw [walkWindow]
        exact SldAreConvertibleLayers.fromSymmetry slideInstance
      exact SldAreConvertibleLayers.fromTransitivity gadgetMuWithSuffix
        (SldAreConvertibleLayers.fromTransitivity recursionAfterGadgets blockSlideBack)

/-- THE MU FAN-DUPLICATION STATEMENT IS INHABITED (ascription against the live Prop). -/
theorem lcoMuFanDuplicationHolds : lstMuFanDuplicationStatement :=
  fun vectorLength columnEntries => lcoMuFanDuplication vectorLength columnEntries



/-! ## SCALE-FUSION: two scale towers over a copied strand fuse into the summed tower -/

/-- SCALE-FUSION: copy, scale the branches, add — that IS the summed tower:
`delta ; (scale(a) | scale(b)) ; mu ~ scale(a + b)`.  Induction on the first factor: the
zero case discards one branch (C2) and the fresh zero dies into the add (M2); the successor
case peels one copy-add pair through coassociativity and slides, the induction hypothesis
fuses the shorter towers, and the re-emitted crossing dies by the mirrored tower crossing
plus one commutativity fire. -/
theorem lcoScaleTowersFuseOverCopy : (firstFactor secondFactor : Nat) ->
    SldAreConvertibleLayers 1
      ([SldCell.generatorDelta]
        :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
              [[SldCell.generatorMu]]))
      (lstScaleLayerList (firstFactor + secondFactor))
  | 0, secondFactor => by
      rw [Nat.zero_add, lstScaleZeroLayerShape]
      have counitFires : SldAreConvertibleLayers 1
          ([SldCell.generatorDelta] :: [SldCell.generatorEpsilon, SldCell.wire]
            :: [SldCell.generatorEta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                [[SldCell.generatorMu]])
          ([SldCell.generatorEta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                [[SldCell.generatorMu]]) :=
        SldAreConvertibleLayers.fromCopyLeftCounitRow 0 0
          ([SldCell.generatorEta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                [[SldCell.generatorMu]])
      have zeroSlides : SldAreConvertibleLayers 1
          ([SldCell.generatorEta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                [[SldCell.generatorMu]])
          (sldAppendLayers (lstScaleLayerList secondFactor)
            ([SldCell.generatorEta, SldCell.wire] :: [[SldCell.generatorMu]])) := by
        have slideInstance := sldUpperLayerSlidesDownPastBlock [SldCell.generatorEta]
          (lstScaleLayerList secondFactor) 1 (lstScaleLayersAreComposable secondFactor)
          [[SldCell.generatorMu]]
        rw [show sldLayerSourceArity [SldCell.generatorEta] = 0 from rfl,
          show sldLayerTargetArity [SldCell.generatorEta] = 1 from rfl,
          lstScaleLayersReach, sldPadLayersAboveWithZeroIsSelf] at slideInstance
        exact slideInstance
      have leftUnitFires : SldAreConvertibleLayers 1
          (sldAppendLayers (lstScaleLayerList secondFactor)
            ([SldCell.generatorEta, SldCell.wire] :: [[SldCell.generatorMu]]))
          (sldAppendLayers (lstScaleLayerList secondFactor) []) := by
        refine sldConvUnderPrefixList (lstScaleLayerList secondFactor) 1 _ _ ?_
        rw [lstScaleLayersReach]
        exact SldAreConvertibleLayers.fromAddLeftUnitRow 0 0 []
      rw [sldAppendLayersNilRightIsSelf] at leftUnitFires
      exact SldAreConvertibleLayers.fromTransitivity counitFires
        (SldAreConvertibleLayers.fromTransitivity zeroSlides leftUnitFires)
  | firstPred + 1, secondFactor => by
      rw [Nat.succ_add, lstScaleSuccUnfolds (firstPred + secondFactor),
        lstScaleSuccUnfolds firstPred]
      have leftShape : sldPadLayersBelow 1
          (sldAppendLayers [[SldCell.generatorDelta]]
            (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
              [[SldCell.generatorMu]]))
          = [SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList firstPred))
                [[SldCell.generatorMu, SldCell.wire]] := by
        rw [sldPadLayersBelowOfAppend, sldPadLayersBelowOfAppend, lstPadLayersBelowCompose]
        rfl
      rw [leftShape]
      show SldAreConvertibleLayers 1
        ([SldCell.generatorDelta]
          :: [SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers
              (sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList firstPred))
                [[SldCell.generatorMu, SldCell.wire]])
              (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                [[SldCell.generatorMu]]))
        ([SldCell.generatorDelta]
          :: sldAppendLayers
              (sldPadLayersBelow 1 (lstScaleLayerList (firstPred + secondFactor)))
              [[SldCell.generatorMu]])
      rw [sldAppendLayersAssoc (sldPadLayersBelow 2 (lstScaleLayerList firstPred))
        [[SldCell.generatorMu, SldCell.wire]]]
      have coassocFires : SldAreConvertibleLayers 1
          ([SldCell.generatorDelta]
            :: [SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList firstPred))
                ([SldCell.generatorMu, SldCell.wire]
                  :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                      [[SldCell.generatorMu]]))
          ([SldCell.generatorDelta]
            :: [SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList firstPred))
                ([SldCell.generatorMu, SldCell.wire]
                  :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                      [[SldCell.generatorMu]])) :=
        SldAreConvertibleLayers.fromCopyCoassociativityRow 0 0
          (sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList firstPred))
            ([SldCell.generatorMu, SldCell.wire]
              :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                  [[SldCell.generatorMu]]))
      have freshCopySlides : SldAreConvertibleLayers 1
          ([SldCell.generatorDelta]
            :: [SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList firstPred))
                ([SldCell.generatorMu, SldCell.wire]
                  :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                      [[SldCell.generatorMu]]))
          ([SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                ([SldCell.wire, SldCell.generatorDelta]
                  :: [SldCell.generatorMu, SldCell.wire]
                  :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                      [[SldCell.generatorMu]])) := by
        have slideInstance := sldLowerLayerSlidesDownPastBlock [SldCell.generatorDelta]
          (lstScaleLayerList firstPred) 1 (lstScaleLayersAreComposable firstPred)
          ([SldCell.generatorMu, SldCell.wire]
            :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                [[SldCell.generatorMu]])
        rw [lstScaleLayersReach] at slideInstance
        exact SldAreConvertibleLayers.underLayerPrefix 1 [SldCell.generatorDelta]
          slideInstance
      have addSlides : SldAreConvertibleLayers 3
          ([SldCell.generatorMu, SldCell.wire]
            :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                [[SldCell.generatorMu]])
          (sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
            ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: [])) := by
        have slideInstance := sldUpperLayerSlidesDownPastBlock [SldCell.generatorMu]
          (lstScaleLayerList secondFactor) 1 (lstScaleLayersAreComposable secondFactor)
          [[SldCell.generatorMu]]
        rw [lstScaleLayersReach] at slideInstance
        exact slideInstance
      have addSlideUnderPrefix : SldAreConvertibleLayers 1
          ([SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                ([SldCell.wire, SldCell.generatorDelta]
                  :: [SldCell.generatorMu, SldCell.wire]
                  :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                      [[SldCell.generatorMu]]))
          ([SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                ([SldCell.wire, SldCell.generatorDelta]
                  :: sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
                      ([SldCell.generatorMu, SldCell.wire]
                        :: [SldCell.generatorMu] :: []))) := by
        have prefixReach : sldLayersTargetArityFrom 1
            ([SldCell.generatorDelta]
              :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                  [[SldCell.wire, SldCell.generatorDelta]]) = 3 := by
          show sldLayersTargetArityFrom 2
            (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
              [[SldCell.wire, SldCell.generatorDelta]]) = 3
          rw [sldAppendLayersTargetArityFrom]
          have belowReach : sldLayersTargetArityFrom 2
              (sldPadLayersBelow 1 (lstScaleLayerList firstPred)) = 2 := by
            have liftedReach := sldPadLayersBelowTargetArityFrom 1
              (lstScaleLayerList firstPred) 1
            rw [lstScaleLayersReach] at liftedReach
            exact liftedReach
          rw [belowReach]
          rfl
        have core : SldAreConvertibleLayers 1
            (sldAppendLayers
              ([SldCell.generatorDelta]
                :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    [[SldCell.wire, SldCell.generatorDelta]])
              ([SldCell.generatorMu, SldCell.wire]
                :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                    [[SldCell.generatorMu]]))
            (sldAppendLayers
              ([SldCell.generatorDelta]
                :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    [[SldCell.wire, SldCell.generatorDelta]])
              (sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
                ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: []))) := by
          refine sldConvUnderPrefixList
            ([SldCell.generatorDelta]
              :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                  [[SldCell.wire, SldCell.generatorDelta]]) 1 _ _ ?_
          rw [prefixReach]
          exact addSlides
        rw [show sldAppendLayers
              ([SldCell.generatorDelta]
                :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    [[SldCell.wire, SldCell.generatorDelta]])
              ([SldCell.generatorMu, SldCell.wire]
                :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                    [[SldCell.generatorMu]])
            = [SldCell.generatorDelta]
              :: sldAppendLayers
                  (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    [[SldCell.wire, SldCell.generatorDelta]])
                  ([SldCell.generatorMu, SldCell.wire]
                    :: sldAppendLayers
                        (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                        [[SldCell.generatorMu]]) from rfl,
          sldAppendLayersAssoc,
          show sldAppendLayers
              ([SldCell.generatorDelta]
                :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    [[SldCell.wire, SldCell.generatorDelta]])
              (sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
                ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: []))
            = [SldCell.generatorDelta]
              :: sldAppendLayers
                  (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    [[SldCell.wire, SldCell.generatorDelta]])
                  (sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
                    ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: []))
            from rfl,
          sldAppendLayersAssoc] at core
        exact core
      have recursionRefolds : SldAreConvertibleLayers 1
          ([SldCell.generatorDelta]
            :: sldAppendLayers
                (sldPadLayersBelow 1 (lstScaleLayerList (firstPred + secondFactor)))
                [[SldCell.generatorMu]])
          ([SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                ([SldCell.wire, SldCell.generatorDelta]
                  :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                      ([SldCell.generatorMu, SldCell.wire]
                        :: [SldCell.generatorMu] :: []))) := by
        have paddedRecursion := sldConvPadsBelow
          (SldAreConvertibleLayers.fromSymmetry
            (lcoScaleTowersFuseOverCopy firstPred secondFactor)) 1
        rw [show sldPadLayersBelow 1
              ([SldCell.generatorDelta]
                :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                      [[SldCell.generatorMu]]))
            = [SldCell.generatorDelta, SldCell.wire]
              :: sldPadLayersBelow 1
                  (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor))
                      [[SldCell.generatorMu]])) from rfl,
          sldPadLayersBelowOfAppend, sldPadLayersBelowOfAppend, lstPadLayersBelowCompose,
          lstPadBelowOfPadAboveIsPadWindow] at paddedRecursion
        have withSuffix := sldConvAppendsSuffix paddedRecursion [[SldCell.generatorMu]]
        rw [show sldAppendLayers
              ([SldCell.generatorDelta, SldCell.wire]
                :: sldAppendLayers (sldPadLayersBelow (1 + 1) (lstScaleLayerList firstPred))
                    (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                      (sldPadLayersBelow 1 [[SldCell.generatorMu]])))
              [[SldCell.generatorMu]]
            = [SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers
                  (sldAppendLayers (sldPadLayersBelow (1 + 1) (lstScaleLayerList firstPred))
                    (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                      (sldPadLayersBelow 1 [[SldCell.generatorMu]])))
                  [[SldCell.generatorMu]] from rfl,
          sldAppendLayersAssoc, sldAppendLayersAssoc] at withSuffix
        have underCopy := SldAreConvertibleLayers.underLayerPrefix 1
          [SldCell.generatorDelta] withSuffix
        -- Reassociate the double copy at the head and slide the fresh copy below the
        -- first tower, meeting the left-spine form.
        have coassocBack : SldAreConvertibleLayers 1
            ([SldCell.generatorDelta]
              :: [SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList firstPred))
                  (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                    ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: [])))
            ([SldCell.generatorDelta]
              :: [SldCell.wire, SldCell.generatorDelta]
              :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList firstPred))
                  (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                    ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: []))) :=
          SldAreConvertibleLayers.fromCopyCoassociativityRow 0 0
            (sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList firstPred))
              (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: [])))
        have freshSlideBack : SldAreConvertibleLayers 1
            ([SldCell.generatorDelta]
              :: [SldCell.wire, SldCell.generatorDelta]
              :: sldAppendLayers (sldPadLayersBelow 2 (lstScaleLayerList firstPred))
                  (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                    ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: [])))
            ([SldCell.generatorDelta]
              :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                  ([SldCell.wire, SldCell.generatorDelta]
                    :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                        ([SldCell.generatorMu, SldCell.wire]
                          :: [SldCell.generatorMu] :: []))) := by
          have slideInstance := sldLowerLayerSlidesDownPastBlock [SldCell.generatorDelta]
            (lstScaleLayerList firstPred) 1 (lstScaleLayersAreComposable firstPred)
            (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
              ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: []))
          rw [lstScaleLayersReach] at slideInstance
          exact SldAreConvertibleLayers.underLayerPrefix 1 [SldCell.generatorDelta]
            slideInstance
        exact SldAreConvertibleLayers.fromTransitivity underCopy
          (SldAreConvertibleLayers.fromTransitivity coassocBack freshSlideBack)
      have mirrorCrossFires : SldAreConvertibleLayers 1
          ([SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                ([SldCell.wire, SldCell.generatorDelta]
                  :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                      ([SldCell.generatorMu, SldCell.wire]
                        :: [SldCell.generatorMu] :: [])))
          ([SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                ([SldCell.wire, SldCell.generatorDelta]
                  :: [SldCell.wire, SldCell.crossing]
                  :: sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
                      ([SldCell.wire, SldCell.crossing]
                        :: [SldCell.generatorMu, SldCell.wire]
                        :: [SldCell.generatorMu] :: []))) := by
        have prefixReach : sldLayersTargetArityFrom 1
            ([SldCell.generatorDelta]
              :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                  [[SldCell.wire, SldCell.generatorDelta]]) = 3 := by
          show sldLayersTargetArityFrom 2
            (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
              [[SldCell.wire, SldCell.generatorDelta]]) = 3
          rw [sldAppendLayersTargetArityFrom]
          have belowReach : sldLayersTargetArityFrom 2
              (sldPadLayersBelow 1 (lstScaleLayerList firstPred)) = 2 := by
            have liftedReach := sldPadLayersBelowTargetArityFrom 1
              (lstScaleLayerList firstPred) 1
            rw [lstScaleLayersReach] at liftedReach
            exact liftedReach
          rw [belowReach]
          rfl
        have mirrorPadded := sldConvPadsAbove
          (lcoSwapDescendsIntoScaleTower secondFactor) 1
        rw [show sldPadLayersAbove 1
              ([SldCell.crossing] :: sldPadLayersBelow 1 (lstScaleLayerList secondFactor))
            = [SldCell.wire, SldCell.crossing]
              :: sldPadLayersAbove 1
                  (sldPadLayersBelow 1 (lstScaleLayerList secondFactor)) from rfl,
          lstPadAboveOfPadBelowIsPadWindow, sldPadLayersAboveOfAppend,
          lstPadLayersAboveCompose] at mirrorPadded
        have mirrorWithSuffix := sldConvAppendsSuffix mirrorPadded
          ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: [])
        rw [sldAppendLayersAssoc] at mirrorWithSuffix
        have pairThenMirror : SldAreConvertibleLayers 3
            (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
              ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: []))
            ([SldCell.wire, SldCell.crossing]
              :: sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
                  ([SldCell.wire, SldCell.crossing]
                    :: [SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.generatorMu] :: [])) := by
          have tauPairMaterializes : SldAreConvertibleLayers 3
              (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: []))
              ([SldCell.wire, SldCell.crossing] :: [SldCell.wire, SldCell.crossing]
                :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                    ([SldCell.generatorMu, SldCell.wire]
                      :: [SldCell.generatorMu] :: [])) :=
            SldAreConvertibleLayers.fromSymmetry
              (SldAreConvertibleLayers.fromSwapInvolutionRow 1 0
                (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: [])))
          have mirrorFires : SldAreConvertibleLayers 3
              ([SldCell.wire, SldCell.crossing] :: [SldCell.wire, SldCell.crossing]
                :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                    ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: []))
              ([SldCell.wire, SldCell.crossing]
                :: sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
                    ([SldCell.wire, SldCell.crossing]
                      :: [SldCell.generatorMu, SldCell.wire]
                      :: [SldCell.generatorMu] :: [])) :=
            SldAreConvertibleLayers.underLayerPrefix 3 [SldCell.wire, SldCell.crossing]
              mirrorWithSuffix
          exact SldAreConvertibleLayers.fromTransitivity tauPairMaterializes mirrorFires
        have core : SldAreConvertibleLayers 1
            (sldAppendLayers
              ([SldCell.generatorDelta]
                :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    [[SldCell.wire, SldCell.generatorDelta]])
              (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: [])))
            (sldAppendLayers
              ([SldCell.generatorDelta]
                :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    [[SldCell.wire, SldCell.generatorDelta]])
              ([SldCell.wire, SldCell.crossing]
                :: sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
                    ([SldCell.wire, SldCell.crossing]
                      :: [SldCell.generatorMu, SldCell.wire]
                      :: [SldCell.generatorMu] :: []))) := by
          refine sldConvUnderPrefixList
            ([SldCell.generatorDelta]
              :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                  [[SldCell.wire, SldCell.generatorDelta]]) 1 _ _ ?_
          rw [prefixReach]
          exact pairThenMirror
        rw [show sldAppendLayers
              ([SldCell.generatorDelta]
                :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    [[SldCell.wire, SldCell.generatorDelta]])
              (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: []))
            = [SldCell.generatorDelta]
              :: sldAppendLayers
                  (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    [[SldCell.wire, SldCell.generatorDelta]])
                  (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
                    ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: []))
            from rfl,
          sldAppendLayersAssoc,
          show sldAppendLayers
              ([SldCell.generatorDelta]
                :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    [[SldCell.wire, SldCell.generatorDelta]])
              ([SldCell.wire, SldCell.crossing]
                :: sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
                    ([SldCell.wire, SldCell.crossing]
                      :: [SldCell.generatorMu, SldCell.wire]
                      :: [SldCell.generatorMu] :: []))
            = [SldCell.generatorDelta]
              :: sldAppendLayers
                  (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    [[SldCell.wire, SldCell.generatorDelta]])
                  ([SldCell.wire, SldCell.crossing]
                    :: sldAppendLayers
                        (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
                        ([SldCell.wire, SldCell.crossing]
                          :: [SldCell.generatorMu, SldCell.wire]
                          :: [SldCell.generatorMu] :: [])) from rfl,
          sldAppendLayersAssoc] at core
        exact core
      have cocommKillsCross : SldAreConvertibleLayers 1
          ([SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                ([SldCell.wire, SldCell.generatorDelta]
                  :: [SldCell.wire, SldCell.crossing]
                  :: sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
                      ([SldCell.wire, SldCell.crossing]
                        :: [SldCell.generatorMu, SldCell.wire]
                        :: [SldCell.generatorMu] :: [])))
          ([SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                ([SldCell.wire, SldCell.generatorDelta]
                  :: sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
                      ([SldCell.wire, SldCell.crossing]
                        :: [SldCell.generatorMu, SldCell.wire]
                        :: [SldCell.generatorMu] :: []))) := by
        have prefixReach : sldLayersTargetArityFrom 1
            ([SldCell.generatorDelta]
              :: sldPadLayersBelow 1 (lstScaleLayerList firstPred)) = 2 := by
          show sldLayersTargetArityFrom 2
            (sldPadLayersBelow 1 (lstScaleLayerList firstPred)) = 2
          have liftedReach := sldPadLayersBelowTargetArityFrom 1
            (lstScaleLayerList firstPred) 1
          rw [lstScaleLayersReach] at liftedReach
          exact liftedReach
        refine sldConvUnderPrefixList
          ([SldCell.generatorDelta]
            :: sldPadLayersBelow 1 (lstScaleLayerList firstPred)) 1 _ _ ?_
        rw [prefixReach]
        exact SldAreConvertibleLayers.fromCopyCocommutativityRow 1 0
          (sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
            ([SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire]
              :: [SldCell.generatorMu] :: []))
      have crossDiesInAdd : SldAreConvertibleLayers 1
          ([SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                ([SldCell.wire, SldCell.generatorDelta]
                  :: sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
                      ([SldCell.wire, SldCell.crossing]
                        :: [SldCell.generatorMu, SldCell.wire]
                        :: [SldCell.generatorMu] :: [])))
          ([SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                ([SldCell.wire, SldCell.generatorDelta]
                  :: sldAppendLayers (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))
                      ([SldCell.generatorMu, SldCell.wire]
                        :: [SldCell.generatorMu] :: []))) := by
        have swapAddFires : SldAreConvertibleLayers 3
            ([SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire]
              :: [SldCell.generatorMu] :: [])
            ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: []) := by
          have rerouted := lcoSwapThenUpperAddReroutes ([SldCell.generatorMu] :: [])
          have tailCommutes : SldAreConvertibleLayers 3
              ([SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu]
                :: [SldCell.crossing] :: [SldCell.generatorMu] :: [])
              ([SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu] :: []) :=
            sldConvUnderPrefixList
              [[SldCell.crossing, SldCell.wire], [SldCell.wire, SldCell.generatorMu]] 3 _ _
              (SldAreConvertibleLayers.fromAddCommutativityRow 0 0 [])
          have assocBack : SldAreConvertibleLayers 3
              ([SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.generatorMu]
                :: [SldCell.generatorMu] :: [])
              ([SldCell.crossing, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire]
                :: [SldCell.generatorMu] :: []) :=
            SldAreConvertibleLayers.underLayerPrefix 3 [SldCell.crossing, SldCell.wire]
              (SldAreConvertibleLayers.fromSymmetry
                (SldAreConvertibleLayers.fromAddAssociativityRow 0 0 []))
          have headCommutes : SldAreConvertibleLayers 3
              ([SldCell.crossing, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire]
                :: [SldCell.generatorMu] :: [])
              ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: []) :=
            SldAreConvertibleLayers.fromAddCommutativityRow 0 1
              ([SldCell.generatorMu] :: [])
          exact SldAreConvertibleLayers.fromTransitivity rerouted
            (SldAreConvertibleLayers.fromTransitivity tailCommutes
              (SldAreConvertibleLayers.fromTransitivity assocBack headCommutes))
        have prefixReach : sldLayersTargetArityFrom 1
            ([SldCell.generatorDelta]
              :: sldAppendLayers
                  (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    [[SldCell.wire, SldCell.generatorDelta]])
                  (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))) = 3 := by
          show sldLayersTargetArityFrom 2
            (sldAppendLayers
              (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                [[SldCell.wire, SldCell.generatorDelta]])
              (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))) = 3
          rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom]
          have belowReach : sldLayersTargetArityFrom 2
              (sldPadLayersBelow 1 (lstScaleLayerList firstPred)) = 2 := by
            have liftedReach := sldPadLayersBelowTargetArityFrom 1
              (lstScaleLayerList firstPred) 1
            rw [lstScaleLayersReach] at liftedReach
            exact liftedReach
          rw [belowReach]
          have aboveReach := sldPadLayersAboveTargetArityFrom 2
            (lstScaleLayerList secondFactor) 1
          rw [lstScaleLayersReach] at aboveReach
          exact aboveReach
        have core : SldAreConvertibleLayers 1
            (sldAppendLayers
              ([SldCell.generatorDelta]
                :: sldAppendLayers
                    (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                      [[SldCell.wire, SldCell.generatorDelta]])
                    (sldPadLayersAbove 2 (lstScaleLayerList secondFactor)))
              ([SldCell.wire, SldCell.crossing]
                :: [SldCell.generatorMu, SldCell.wire]
                :: [SldCell.generatorMu] :: []))
            (sldAppendLayers
              ([SldCell.generatorDelta]
                :: sldAppendLayers
                    (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                      [[SldCell.wire, SldCell.generatorDelta]])
                    (sldPadLayersAbove 2 (lstScaleLayerList secondFactor)))
              ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: [])) := by
          refine sldConvUnderPrefixList
            ([SldCell.generatorDelta]
              :: sldAppendLayers
                  (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                    [[SldCell.wire, SldCell.generatorDelta]])
                  (sldPadLayersAbove 2 (lstScaleLayerList secondFactor))) 1 _ _ ?_
          rw [prefixReach]
          exact swapAddFires
        rw [show sldAppendLayers
              ([SldCell.generatorDelta]
                :: sldAppendLayers
                    (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                      [[SldCell.wire, SldCell.generatorDelta]])
                    (sldPadLayersAbove 2 (lstScaleLayerList secondFactor)))
              ([SldCell.wire, SldCell.crossing]
                :: [SldCell.generatorMu, SldCell.wire]
                :: [SldCell.generatorMu] :: [])
            = [SldCell.generatorDelta]
              :: sldAppendLayers
                  (sldAppendLayers
                    (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                      [[SldCell.wire, SldCell.generatorDelta]])
                    (sldPadLayersAbove 2 (lstScaleLayerList secondFactor)))
                  ([SldCell.wire, SldCell.crossing]
                    :: [SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.generatorMu] :: []) from rfl,
          sldAppendLayersAssoc, sldAppendLayersAssoc,
          show sldAppendLayers
              ([SldCell.generatorDelta]
                :: sldAppendLayers
                    (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                      [[SldCell.wire, SldCell.generatorDelta]])
                    (sldPadLayersAbove 2 (lstScaleLayerList secondFactor)))
              ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: [])
            = [SldCell.generatorDelta]
              :: sldAppendLayers
                  (sldAppendLayers
                    (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstPred))
                      [[SldCell.wire, SldCell.generatorDelta]])
                    (sldPadLayersAbove 2 (lstScaleLayerList secondFactor)))
                  ([SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu] :: [])
            from rfl,
          sldAppendLayersAssoc, sldAppendLayersAssoc] at core
        exact core
      exact SldAreConvertibleLayers.fromTransitivity coassocFires
        (SldAreConvertibleLayers.fromTransitivity freshCopySlides
          (SldAreConvertibleLayers.fromTransitivity addSlideUnderPrefix
            (SldAreConvertibleLayers.fromSymmetry
              (SldAreConvertibleLayers.fromTransitivity recursionRefolds
                (SldAreConvertibleLayers.fromTransitivity mirrorCrossFires
                  (SldAreConvertibleLayers.fromTransitivity cocommKillsCross
                    crossDiesInAdd))))))


/-! ## The copy-tree kit (dual of the add-tree kit) -/

/-- Reassociation of the balanced four-leaf copy tree into the mid-splitting tree
(three coassociativity fires). -/
theorem lcoBalancedCopyTreeReassociates (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 1
      ([SldCell.generatorDelta]
        :: [SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: suffixLayers)
      ([SldCell.generatorDelta]
        :: [SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: suffixLayers) := by
  have headReassociates : SldAreConvertibleLayers 1
      ([SldCell.generatorDelta]
        :: [SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: suffixLayers)
      ([SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: suffixLayers) :=
    SldAreConvertibleLayers.fromCopyCoassociativityRow 0 0
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: suffixLayers)
  have innerReassociates : SldAreConvertibleLayers 1
      ([SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: suffixLayers)
      ([SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: suffixLayers) :=
    SldAreConvertibleLayers.underLayerPrefix 1 [SldCell.generatorDelta]
      (SldAreConvertibleLayers.fromSymmetry
        (SldAreConvertibleLayers.fromCopyCoassociativityRow 1 0 suffixLayers))
  have headBack : SldAreConvertibleLayers 1
      ([SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: suffixLayers)
      ([SldCell.generatorDelta]
        :: [SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: suffixLayers) :=
    SldAreConvertibleLayers.fromSymmetry
      (SldAreConvertibleLayers.fromCopyCoassociativityRow 0 0
        ([SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: suffixLayers))
  exact SldAreConvertibleLayers.fromTransitivity headReassociates
    (SldAreConvertibleLayers.fromTransitivity innerReassociates headBack)

/-- The balanced four-leaf copy tree absorbs a following middle crossing (reassociate,
one cocommutativity fire at the padded middle copy, reassociate back). -/
theorem lcoCopyTreeAbsorbsMidSwap (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 1
      ([SldCell.generatorDelta]
        :: [SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire] :: suffixLayers)
      ([SldCell.generatorDelta]
        :: [SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: suffixLayers) := by
  have treeLeans := lcoBalancedCopyTreeReassociates
    ([SldCell.wire, SldCell.crossing, SldCell.wire] :: suffixLayers)
  have cocommFires : SldAreConvertibleLayers 1
      ([SldCell.generatorDelta]
        :: [SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire] :: suffixLayers)
      ([SldCell.generatorDelta]
        :: [SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: suffixLayers) :=
    sldConvUnderPrefixList
      [[SldCell.generatorDelta], [SldCell.generatorDelta, SldCell.wire]] 1 _ _
      (SldAreConvertibleLayers.fromCopyCocommutativityRow 1 1 suffixLayers)
  exact SldAreConvertibleLayers.fromTransitivity treeLeans
    (SldAreConvertibleLayers.fromTransitivity cocommFires
      (SldAreConvertibleLayers.fromSymmetry (lcoBalancedCopyTreeReassociates suffixLayers)))

/-- The crossing-then-lower-copy reroute: `(w | tau) ; (delta | w) ~ tau ; (w | delta) ;
(tau | w)` read with the crossing entering above. -/
theorem lcoCopyBelowCrossingReroutes (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 2
      ([SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers)
      ([SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.crossing, SldCell.wire] :: suffixLayers) := by
  have tauPairAppends : SldAreConvertibleLayers 2
      ([SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers)
      ([SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire] :: suffixLayers) :=
    sldConvUnderPrefixList
      [[SldCell.generatorDelta, SldCell.wire], [SldCell.wire, SldCell.crossing]] 2 _ _
      (SldAreConvertibleLayers.fromSymmetry
        (SldAreConvertibleLayers.fromSwapInvolutionRow 0 1 suffixLayers))
  have kitFires : SldAreConvertibleLayers 2
      ([SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire] :: suffixLayers)
      ([SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.crossing, SldCell.wire] :: suffixLayers) :=
    lcoCopySlidesBelowParkedStrand ([SldCell.crossing, SldCell.wire] :: suffixLayers)
  exact SldAreConvertibleLayers.fromTransitivity tauPairAppends kitFires


/-- THE FIVE-STRAND COPY-ROUTE ALIGNMENT: the fused-gadget spine with the crossing entering
above converts to the two-gadget spine with the accumulator descending first — the dual
partner of the merge-route alignment. -/
theorem lcoFiveStrandCopyRoutesAgree (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers)
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers) := by
  have windowRerouted : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers)
      ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers) := by
    have windowPadded := lcoConvPadsWindow (lcoSwapThenUpperAddReroutes []) 1 1
    have withSuffix := sldConvAppendsSuffix windowPadded
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers)
    exact withSuffix
  have innerRerouted : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers)
      ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers) := by
    have belowPadded := sldConvPadsBelow (lcoSwapThenUpperAddReroutes []) 1
    have withSuffix := sldConvAppendsSuffix belowPadded
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers)
    exact sldConvUnderPrefixList
      [[SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire],
        [SldCell.wire, SldCell.wire, SldCell.generatorMu, SldCell.wire]] 5 _ _ withSuffix
  have tauPairDies : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers)
      ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire],
        [SldCell.wire, SldCell.wire, SldCell.generatorMu, SldCell.wire],
        [SldCell.crossing, SldCell.wire, SldCell.wire],
        [SldCell.wire, SldCell.generatorMu, SldCell.wire]] 5 _ _
      (SldAreConvertibleLayers.fromSwapInvolutionRow 0 1
        ([SldCell.wire, SldCell.crossing] :: suffixLayers))
  have addsExchange : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers)
      ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]] 5 _ _
      (SldAreConvertibleLayers.fromSymmetry
        (sldDisjointLayersExchange [SldCell.crossing] [SldCell.generatorMu, SldCell.wire]
          ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing] :: suffixLayers)))
  have assocBack : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers)
      ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire],
        [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]] 5 _ _
      (SldAreConvertibleLayers.fromSymmetry
        (SldAreConvertibleLayers.fromAddAssociativityRow 1 1
          ([SldCell.wire, SldCell.crossing] :: suffixLayers)))
  have headRefolds : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers)
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: suffixLayers) :=
    SldAreConvertibleLayers.fromSymmetry
      (SldAreConvertibleLayers.fromSwapPastAddRow 0 2
        ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
          :: [SldCell.wire, SldCell.crossing] :: suffixLayers))
  exact SldAreConvertibleLayers.fromTransitivity windowRerouted
    (SldAreConvertibleLayers.fromTransitivity innerRerouted
      (SldAreConvertibleLayers.fromTransitivity tauPairDies
        (SldAreConvertibleLayers.fromTransitivity addsExchange
          (SldAreConvertibleLayers.fromTransitivity assocBack headRefolds))))


/-! ## GADGET-DELTA: two gadgets over a copied source fuse into the summed gadget -/

/-- GADGET-DELTA: `(wire | delta) ; (gadget(a) | wire) ; (wire | gadget(b)) ~
gadget(a + b) ; (delta | wire)` — the copied source merges with scale a then scale b,
which is one merge with scale a + b, the climbing copy re-emitted by a trailing copy.
Both sides open into the copy-tree head, the two scale windows, and a five-strand
crossing/add spine; SCALE-FUSION fuses the towers, the copy tree absorbs the emitted
crossing, and the copy-route alignment meets the spines. -/
theorem lcoGadgetsFuseOverCopy (firstFactor secondFactor : Nat) :
    SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadLayersBelow 1 (lstGadgetLayerList firstFactor))
            (sldPadLayersAbove 1 (lstGadgetLayerList secondFactor)))
      (sldAppendLayers (lstGadgetLayerList (firstFactor + secondFactor))
        [[SldCell.generatorDelta, SldCell.wire]]) := by
  have windowReachA : sldLayersTargetArityFrom 3 (sldPadWindow 1 1 (lstScaleLayerList firstFactor)) = 3 := by
    have liftedReach := sldPadWindowTargetArityFrom 1 1 (lstScaleLayerList firstFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have windowReachB : sldLayersTargetArityFrom 3 (sldPadWindow 1 1 (lstScaleLayerList secondFactor)) = 3 := by
    have liftedReach := sldPadWindowTargetArityFrom 1 1 (lstScaleLayerList secondFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have windowReachTwelveA : sldLayersTargetArityFrom 4
      (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) = 4 := by
    have liftedReach := sldPadWindowTargetArityFrom 1 2 (lstScaleLayerList firstFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have windowReachThirteenA : sldLayersTargetArityFrom 5
      (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) = 5 := by
    have liftedReach := sldPadWindowTargetArityFrom 1 3 (lstScaleLayerList firstFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have windowReachTwentyOneB : sldLayersTargetArityFrom 4
      (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) = 4 := by
    have liftedReach := sldPadWindowTargetArityFrom 2 1 (lstScaleLayerList secondFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have aboveReachA : sldLayersTargetArityFrom 2 (sldPadLayersAbove 1 (lstScaleLayerList firstFactor)) = 2 := by
    have liftedReach := sldPadLayersAboveTargetArityFrom 1 (lstScaleLayerList firstFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have belowReachB : sldLayersTargetArityFrom 2 (sldPadLayersBelow 1 (lstScaleLayerList secondFactor)) = 2 := by
    have liftedReach := sldPadLayersBelowTargetArityFrom 1 (lstScaleLayerList secondFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have aboveReachTwoB : sldLayersTargetArityFrom 3
      (sldPadLayersAbove 2 (lstScaleLayerList secondFactor)) = 3 := by
    have liftedReach := sldPadLayersAboveTargetArityFrom 2 (lstScaleLayerList secondFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have padBelowShape : sldPadLayersBelow 1
      (sldAppendLayers [[SldCell.wire, SldCell.generatorDelta]]
        (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]))
      = [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: []) := by
    rw [sldPadLayersBelowOfAppend, sldPadLayersBelowOfAppend, sldPadLayersBelowOfPadWindow]
    rfl
  have padAboveShape : sldPadLayersAbove 1
      (sldAppendLayers [[SldCell.wire, SldCell.generatorDelta]]
        (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList secondFactor)) [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]))
      = [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []) := by
    rw [sldPadLayersAboveOfAppend, sldPadLayersAboveOfAppend, sldPadLayersAboveOfPadWindow]
    rfl
  rw [lstGadgetLayerShape firstFactor, lstGadgetLayerShape secondFactor,
    lstGadgetLayerShape (firstFactor + secondFactor), padBelowShape, padAboveShape]
  show SldAreConvertibleLayers 2
    ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
      :: sldAppendLayers
          (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: []))
          ([SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
    (sldAppendLayers
      (sldAppendLayers [[SldCell.wire, SldCell.generatorDelta]]
        (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList (firstFactor + secondFactor)))
          [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]))
      [[SldCell.generatorDelta, SldCell.wire]])
  rw [sldAppendLayersAssoc (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [])]
  show SldAreConvertibleLayers 2
    ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
      :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
          ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
    ([SldCell.wire, SldCell.generatorDelta]
      :: sldAppendLayers
          (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList (firstFactor + secondFactor)))
            [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]])
          [[SldCell.generatorDelta, SldCell.wire]])
  rw [sldAppendLayersAssoc (sldPadWindow 1 1 (lstScaleLayerList (firstFactor + secondFactor)))
    [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]] [[SldCell.generatorDelta, SldCell.wire]]]
  -- LEFT SPINE
  have crossCopyExchange : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.crossing, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have prefixReach : sldLayersTargetArityFrom 2
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire]]) = 3 := by
      show sldLayersTargetArityFrom 4
        (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire]]) = 3
      rw [sldAppendLayersTargetArityFrom, windowReachTwelveA]
      rfl
    have core : SldAreConvertibleLayers 2
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire]])
          ([SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire]])
          ([SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.crossing, SldCell.wire, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
      refine sldConvUnderPrefixList
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire]])
        2 _ _ ?_
      rw [prefixReach]
      exact sldDisjointLayersExchange [SldCell.crossing] [SldCell.generatorDelta]
        (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
    rw [show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire]])
          ([SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
        = [SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire]])
              ([SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
                :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
        from rfl,
      sldAppendLayersAssoc,
      show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire]])
          ([SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.crossing, SldCell.wire, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
        = [SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire]])
              ([SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.crossing, SldCell.wire, SldCell.wire]
                :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
        from rfl,
      sldAppendLayersAssoc] at core
    exact core
  have addCopyExchange : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.crossing, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have prefixReach : sldLayersTargetArityFrom 2
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: sldPadWindow 1 2 (lstScaleLayerList firstFactor)) = 4 := by
      show sldLayersTargetArityFrom 4 (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) = 4
      exact windowReachTwelveA
    refine sldConvUnderPrefixList
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: sldPadWindow 1 2 (lstScaleLayerList firstFactor)) 2 _ _ ?_
    rw [prefixReach]
    exact sldDisjointLayersExchange [SldCell.generatorMu] [SldCell.wire, SldCell.generatorDelta]
      ([SldCell.crossing, SldCell.wire, SldCell.wire] :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
  have copySlidesLeft : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have slideInstance := sldLowerLayerSlidesDownPastBlock [SldCell.generatorDelta]
      (sldPadWindow 1 1 (lstScaleLayerList firstFactor)) 3
      (sldPadWindowIsComposableFrom 1 1 (lstScaleLayerList firstFactor) 1
        (lstScaleLayersAreComposable firstFactor))
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
    rw [windowReachA, sldPadLayersBelowOfPadWindow,
      sldPadLayersBelowOfPadWindow] at slideInstance
    exact sldConvUnderPrefixList [[SldCell.wire, SldCell.generatorDelta], [SldCell.wire, SldCell.generatorDelta, SldCell.wire]] 2 _ _
      (SldAreConvertibleLayers.fromSymmetry slideInstance)
  have crossSlidesLeft : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor))
                  ([SldCell.crossing, SldCell.wire, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have slideInstance := sldUpperLayerSlidesDownPastBlock [SldCell.crossing]
      (sldPadLayersBelow 1 (lstScaleLayerList secondFactor)) 2
      (sldPadLayersBelowAreComposableFrom 1 (lstScaleLayerList secondFactor) 1
        (lstScaleLayersAreComposable secondFactor))
      ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])
    rw [belowReachB, lstPadAboveOfPadBelowIsPadWindow,
      lstPadAboveOfPadBelowIsPadWindow] at slideInstance
    have prefixReach : sldLayersTargetArityFrom 2
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]]) = 4 := by
      show sldLayersTargetArityFrom 5
        (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]]) = 4
      rw [sldAppendLayersTargetArityFrom, windowReachThirteenA]
      rfl
    have core : SldAreConvertibleLayers 2
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]])
          ([SldCell.crossing, SldCell.wire, SldCell.wire] :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]])
          (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.crossing, SldCell.wire, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
      refine sldConvUnderPrefixList
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]]) 2 _ _ ?_
      rw [prefixReach]
      exact slideInstance
    rw [show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]])
          ([SldCell.crossing, SldCell.wire, SldCell.wire] :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
        = [SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]])
              ([SldCell.crossing, SldCell.wire, SldCell.wire] :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
        from rfl,
      sldAppendLayersAssoc,
      show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]])
          (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.crossing, SldCell.wire, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
        = [SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) [[SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]])
              (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor))
                ([SldCell.crossing, SldCell.wire, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])) from rfl,
      sldAppendLayersAssoc] at core
    exact core
  have addSlidesLeft : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor))
                  ([SldCell.crossing, SldCell.wire, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have slideInstance := sldUpperLayerSlidesDownPastBlock [SldCell.generatorMu]
      (sldPadWindow 1 1 (lstScaleLayerList secondFactor)) 3
      (sldPadWindowIsComposableFrom 1 1 (lstScaleLayerList secondFactor) 1
        (lstScaleLayersAreComposable secondFactor))
      ([SldCell.crossing, SldCell.wire, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])
    rw [windowReachB, sldPadLayersAboveOfPadWindow,
      sldPadLayersAboveOfPadWindow] at slideInstance
    have prefixReach : sldLayersTargetArityFrom 2
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: sldPadWindow 1 3 (lstScaleLayerList firstFactor)) = 5 := by
      show sldLayersTargetArityFrom 5 (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) = 5
      exact windowReachThirteenA
    refine sldConvUnderPrefixList
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: sldPadWindow 1 3 (lstScaleLayerList firstFactor)) 2 _ _ ?_
    rw [prefixReach]
    exact slideInstance
  -- RIGHT SPINE
  have fusionAtWindow : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList (firstFactor + secondFactor)))
            ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [SldCell.generatorDelta, SldCell.wire] :: []))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [SldCell.generatorDelta, SldCell.wire] :: []))) := by
    have windowFused := lcoConvPadsWindow
      (SldAreConvertibleLayers.fromSymmetry
        (lcoScaleTowersFuseOverCopy firstFactor secondFactor)) 1 1
    rw [show sldPadWindow 1 1
          ([SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor)) [[SldCell.generatorMu]]))
        = [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldPadWindow 1 1
              (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList secondFactor)) [[SldCell.generatorMu]])) from rfl,
      lcoPadWindowOfAppendLayers, lcoPadWindowOfAppendLayers,
      lcoPadWindowOfPadLayersBelow, lcoPadWindowOfPadLayersAbove] at windowFused
    have withSuffix := sldConvAppendsSuffix windowFused
      ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [SldCell.generatorDelta, SldCell.wire] :: [])
    rw [show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 (1 + 1) (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadWindow (1 + 1) 1 (lstScaleLayerList secondFactor))
                  (sldPadWindow 1 1 [[SldCell.generatorMu]])))
          ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [SldCell.generatorDelta, SldCell.wire] :: [])
        = [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 (1 + 1) (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadWindow (1 + 1) 1 (lstScaleLayerList secondFactor))
                  (sldPadWindow 1 1 [[SldCell.generatorMu]])))
              ([SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [SldCell.generatorDelta, SldCell.wire] :: []) from rfl,
      sldAppendLayersAssoc, sldAppendLayersAssoc] at withSuffix
    exact SldAreConvertibleLayers.underLayerPrefix 2 [SldCell.wire, SldCell.generatorDelta] withSuffix
  have ndeltaFires : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.crossing] :: [SldCell.generatorDelta, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.generatorDelta] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have prefixReach : sldLayersTargetArityFrom 2
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
              (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: []))) = 2 := by
      show sldLayersTargetArityFrom 4
        (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
          (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: []))) = 2
      rw [sldAppendLayersTargetArityFrom, windowReachTwelveA,
        sldAppendLayersTargetArityFrom, windowReachTwentyOneB]
      rfl
    have core : SldAreConvertibleLayers 2
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: [])))
          ([SldCell.crossing] :: [SldCell.generatorDelta, SldCell.wire] :: []))
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: [])))
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])) := by
      refine sldConvUnderPrefixList
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
              (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: []))) 2 _ _ ?_
      rw [prefixReach]
      exact SldAreConvertibleLayers.fromCopyPastSwapRow 0 0 []
    rw [show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: [])))
          ([SldCell.crossing] :: [SldCell.generatorDelta, SldCell.wire] :: [])
        = [SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: [])))
              ([SldCell.crossing] :: [SldCell.generatorDelta, SldCell.wire] :: []) from rfl,
      sldAppendLayersAssoc, sldAppendLayersAssoc,
      show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: [])))
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])
        = [SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: [])))
              ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []) from rfl,
      sldAppendLayersAssoc, sldAppendLayersAssoc] at core
    have coreShaped : SldAreConvertibleLayers 2
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
              (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor))
                (sldAppendLayers ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: []) ([SldCell.crossing] :: [SldCell.generatorDelta, SldCell.wire] :: []))))
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
              (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor))
                (sldAppendLayers ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: []) ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))) :=
      core
    exact coreShaped
  have addCopyExchangeRight : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.generatorDelta] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have prefixReach : sldLayersTargetArityFrom 2
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
              (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) [[SldCell.wire, SldCell.generatorMu, SldCell.wire]])) = 3 := by
      show sldLayersTargetArityFrom 4
        (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
          (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) [[SldCell.wire, SldCell.generatorMu, SldCell.wire]])) = 3
      rw [sldAppendLayersTargetArityFrom, windowReachTwelveA,
        sldAppendLayersTargetArityFrom, windowReachTwentyOneB]
      rfl
    have core : SldAreConvertibleLayers 2
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) [[SldCell.wire, SldCell.generatorMu, SldCell.wire]]))
          ([SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.generatorDelta] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) [[SldCell.wire, SldCell.generatorMu, SldCell.wire]]))
          ([SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])) := by
      refine sldConvUnderPrefixList
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
              (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) [[SldCell.wire, SldCell.generatorMu, SldCell.wire]])) 2 _ _ ?_
      rw [prefixReach]
      exact sldDisjointLayersExchange [SldCell.generatorMu] [SldCell.generatorDelta] ([SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])
    rw [show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) [[SldCell.wire, SldCell.generatorMu, SldCell.wire]]))
          ([SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.generatorDelta] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])
        = [SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) [[SldCell.wire, SldCell.generatorMu, SldCell.wire]]))
              ([SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.generatorDelta] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []) from rfl,
      sldAppendLayersAssoc, sldAppendLayersAssoc,
      show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) [[SldCell.wire, SldCell.generatorMu, SldCell.wire]]))
          ([SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])
        = [SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor)) [[SldCell.wire, SldCell.generatorMu, SldCell.wire]]))
              ([SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []) from rfl,
      sldAppendLayersAssoc, sldAppendLayersAssoc] at core
    exact core
  have copyAddExchangeRight : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have prefixReach : sldLayersTargetArityFrom 2
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
              (sldPadWindow 2 1 (lstScaleLayerList secondFactor))) = 4 := by
      show sldLayersTargetArityFrom 4
        (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) (sldPadWindow 2 1 (lstScaleLayerList secondFactor))) = 4
      rw [sldAppendLayersTargetArityFrom, windowReachTwelveA]
      exact windowReachTwentyOneB
    have core : SldAreConvertibleLayers 2
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldPadWindow 2 1 (lstScaleLayerList secondFactor)))
          ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldPadWindow 2 1 (lstScaleLayerList secondFactor)))
          ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])) := by
      refine sldConvUnderPrefixList
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
              (sldPadWindow 2 1 (lstScaleLayerList secondFactor))) 2 _ _ ?_
      rw [prefixReach]
      exact sldDisjointLayersExchange [SldCell.wire, SldCell.generatorMu] [SldCell.generatorDelta] ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])
    rw [show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldPadWindow 2 1 (lstScaleLayerList secondFactor)))
          ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])
        = [SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldPadWindow 2 1 (lstScaleLayerList secondFactor)))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []) from rfl,
      sldAppendLayersAssoc,
      show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldPadWindow 2 1 (lstScaleLayerList secondFactor)))
          ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])
        = [SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                (sldPadWindow 2 1 (lstScaleLayerList secondFactor)))
              ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []) from rfl,
      sldAppendLayersAssoc] at core
    exact core
  have copySlidesRightB : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have slideInstance := sldLowerLayerSlidesDownPastBlock [SldCell.generatorDelta]
      (sldPadLayersAbove 2 (lstScaleLayerList secondFactor)) 3
      (sldPadLayersAboveAreComposableFrom 2 (lstScaleLayerList secondFactor) 1
        (lstScaleLayersAreComposable secondFactor))
      ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])
    rw [aboveReachTwoB, lstPadBelowOfPadAboveIsPadWindow,
      lstPadBelowOfPadAboveIsPadWindow] at slideInstance
    have prefixReach : sldLayersTargetArityFrom 2
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: sldPadWindow 1 2 (lstScaleLayerList firstFactor)) = 4 := by
      show sldLayersTargetArityFrom 4 (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) = 4
      exact windowReachTwelveA
    refine sldConvUnderPrefixList
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: sldPadWindow 1 2 (lstScaleLayerList firstFactor)) 2 _ _ ?_
    rw [prefixReach]
    exact SldAreConvertibleLayers.fromSymmetry slideInstance
  have copySlidesRightA : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have slideInstance := sldLowerLayerSlidesDownPastBlock [SldCell.generatorDelta]
      (sldPadWindow 1 1 (lstScaleLayerList firstFactor)) 3
      (sldPadWindowIsComposableFrom 1 1 (lstScaleLayerList firstFactor) 1
        (lstScaleLayersAreComposable firstFactor))
      (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
        ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
    rw [windowReachA, sldPadLayersBelowOfPadWindow,
      sldPadLayersBelowOfPadWindow] at slideInstance
    exact sldConvUnderPrefixList [[SldCell.wire, SldCell.generatorDelta], [SldCell.wire, SldCell.generatorDelta, SldCell.wire]] 2 _ _
      (SldAreConvertibleLayers.fromSymmetry slideInstance)
  -- TAIL ALIGNMENT
  have crossEnters : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have treeAbsorbs := sldConvPadsAbove (lcoCopyTreeAbsorbsMidSwap []) 1
    have withSuffix := sldConvAppendsSuffix
      (SldAreConvertibleLayers.fromSymmetry treeAbsorbs)
      (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
        (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
          ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
    exact withSuffix
  have crossSlidesA : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have slideInstance := sldLowerLayerSlidesDownPastBlock [SldCell.crossing, SldCell.wire]
      (sldPadLayersAbove 1 (lstScaleLayerList firstFactor)) 2
      (sldPadLayersAboveAreComposableFrom 1 (lstScaleLayerList firstFactor) 1
        (lstScaleLayersAreComposable firstFactor))
      (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
        ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
    rw [aboveReachA, lstPadBelowOfPadAboveIsPadWindow,
      lstPadBelowOfPadAboveIsPadWindow] at slideInstance
    exact sldConvUnderPrefixList [[SldCell.wire, SldCell.generatorDelta], [SldCell.wire, SldCell.generatorDelta, SldCell.wire], [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]] 2 _ _ slideInstance
  have crossWindowFires : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have windowPadded := lcoConvPadsWindow (lcoSwapDescendsIntoScaleTower secondFactor) 2 1
    rw [show sldPadWindow 2 1 ([SldCell.crossing] :: sldPadLayersBelow 1 (lstScaleLayerList secondFactor))
        = [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire] :: sldPadWindow 2 1 (sldPadLayersBelow 1 (lstScaleLayerList secondFactor)) from rfl,
      lcoPadWindowOfPadLayersBelow, lcoPadWindowOfAppendLayers,
      lcoPadWindowOfPadLayersAbove] at windowPadded
    have withSuffix := sldConvAppendsSuffix windowPadded
      ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])
    rw [sldAppendLayersAssoc] at withSuffix
    have prefixReach : sldLayersTargetArityFrom 2
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: sldPadWindow 1 3 (lstScaleLayerList firstFactor)) = 5 := by
      show sldLayersTargetArityFrom 5 (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) = 5
      exact windowReachThirteenA
    refine sldConvUnderPrefixList
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta] :: sldPadWindow 1 3 (lstScaleLayerList firstFactor)) 2 _ _ ?_
    rw [prefixReach]
    exact withSuffix
  have spinesAlign : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have prefixReach : sldLayersTargetArityFrom 2
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
              (sldPadWindow 3 1 (lstScaleLayerList secondFactor))) = 5 := by
      show sldLayersTargetArityFrom 5
        (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) (sldPadWindow 3 1 (lstScaleLayerList secondFactor))) = 5
      rw [sldAppendLayersTargetArityFrom, windowReachThirteenA]
      have liftedReach := sldPadWindowTargetArityFrom 3 1 (lstScaleLayerList secondFactor) 1
      rw [lstScaleLayersReach] at liftedReach
      exact liftedReach
    have core : SldAreConvertibleLayers 2
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) (sldPadWindow 3 1 (lstScaleLayerList secondFactor)))
          ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []))
        (sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) (sldPadWindow 3 1 (lstScaleLayerList secondFactor)))
          ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])) := by
      refine sldConvUnderPrefixList
        ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) (sldPadWindow 3 1 (lstScaleLayerList secondFactor)))
        2 _ _ ?_
      rw [prefixReach]
      exact lcoFiveStrandCopyRoutesAgree []
    rw [show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) (sldPadWindow 3 1 (lstScaleLayerList secondFactor)))
          ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])
        = [SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) (sldPadWindow 3 1 (lstScaleLayerList secondFactor)))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []) from rfl,
      sldAppendLayersAssoc,
      show sldAppendLayers
          ([SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) (sldPadWindow 3 1 (lstScaleLayerList secondFactor)))
          ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])
        = [SldCell.wire, SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire] :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
          :: sldAppendLayers
              (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) (sldPadWindow 3 1 (lstScaleLayerList secondFactor)))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire] :: [SldCell.crossing, SldCell.wire, SldCell.wire] :: [SldCell.wire, SldCell.generatorMu, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: []) from rfl,
      sldAppendLayersAssoc] at core
    exact core
  exact SldAreConvertibleLayers.fromTransitivity crossCopyExchange
    (SldAreConvertibleLayers.fromTransitivity addCopyExchange
      (SldAreConvertibleLayers.fromTransitivity copySlidesLeft
        (SldAreConvertibleLayers.fromTransitivity crossSlidesLeft
          (SldAreConvertibleLayers.fromTransitivity addSlidesLeft
            (SldAreConvertibleLayers.fromSymmetry
              (SldAreConvertibleLayers.fromTransitivity fusionAtWindow
                (SldAreConvertibleLayers.fromTransitivity ndeltaFires
                  (SldAreConvertibleLayers.fromTransitivity addCopyExchangeRight
                    (SldAreConvertibleLayers.fromTransitivity copyAddExchangeRight
                      (SldAreConvertibleLayers.fromTransitivity copySlidesRightB
                        (SldAreConvertibleLayers.fromTransitivity copySlidesRightA
                          (SldAreConvertibleLayers.fromTransitivity crossEnters
                            (SldAreConvertibleLayers.fromTransitivity crossSlidesA
                              (SldAreConvertibleLayers.fromTransitivity crossWindowFires
                                spinesAlign))))))))))))))


/-! ## THE DELTA CORE: fan fusion -/

/-- THE DELTA BOTTOM CORE: two fans over one copied source fuse into the sum-column fan —
`(wires(t) | delta) ; (fan(t, A) | wire) ; fan(t, B) ~ fan(t, A + B)` (the derivation
`(acc_i + A_i * x) + B_i * x = acc_i + (A_i + B_i) * x`).  Source-climb induction: the base
is one split plus C3; each rung slides the two gadget blocks together (Godement), fires the
padded GADGET-DELTA, and closes with the below-padded induction hypothesis. -/
theorem lcoDeltaFanFusion : (vectorLength : Nat) -> (firstColumn secondColumn : Nat -> Nat) ->
    SldAreConvertibleLayers (vectorLength + 1)
      (sldAppendCells (sldWireLayerOfArity vectorLength) [SldCell.generatorDelta]
        :: sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList vectorLength firstColumn))
            (lstFanLayerList vectorLength secondColumn))
      (lstFanLayerList vectorLength
        (fun mergeRow => firstColumn mergeRow + secondColumn mergeRow))
  | 0, firstColumn, secondColumn => by
      rw [lstFanZeroLayerShape, lstFanZeroLayerShape, lstFanZeroLayerShape]
      have discardPairJoins : SldAreConvertibleLayers 1
          ([SldCell.generatorDelta] :: [SldCell.generatorEpsilon, SldCell.wire]
            :: [SldCell.generatorEpsilon] :: [])
          ([SldCell.generatorDelta]
            :: [SldCell.generatorEpsilon, SldCell.generatorEpsilon] :: []) :=
        SldAreConvertibleLayers.underLayerPrefix 1 [SldCell.generatorDelta]
          (SldAreConvertibleLayers.fromSymmetry
            (SldAreConvertibleLayers.layerSplitTopActsFirst [SldCell.generatorEpsilon]
              [SldCell.generatorEpsilon] []))
      have discardPairResplits : SldAreConvertibleLayers 1
          ([SldCell.generatorDelta]
            :: [SldCell.generatorEpsilon, SldCell.generatorEpsilon] :: [])
          ([SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorEpsilon]
            :: [SldCell.generatorEpsilon] :: []) :=
        SldAreConvertibleLayers.underLayerPrefix 1 [SldCell.generatorDelta]
          (SldAreConvertibleLayers.layerSplitBottomActsFirst [SldCell.generatorEpsilon]
            [SldCell.generatorEpsilon] [])
      have counitFires : SldAreConvertibleLayers 1
          ([SldCell.generatorDelta] :: [SldCell.wire, SldCell.generatorEpsilon]
            :: [SldCell.generatorEpsilon] :: [])
          ([SldCell.generatorEpsilon] :: []) :=
        SldAreConvertibleLayers.fromCopyRightCounitRow 0 0
          ([SldCell.generatorEpsilon] :: [])
      exact SldAreConvertibleLayers.fromTransitivity discardPairJoins
        (SldAreConvertibleLayers.fromTransitivity discardPairResplits counitFires)
  | vectorLengthPred + 1, firstColumn, secondColumn => by
      rw [lstFanSuccUnfolds vectorLengthPred firstColumn,
        lstFanSuccUnfolds vectorLengthPred secondColumn,
        lstFanSuccUnfolds vectorLengthPred
          (fun mergeRow => firstColumn mergeRow + secondColumn mergeRow)]
      have firstLayerEq : sldAppendCells (sldWireLayerOfArity (vectorLengthPred + 1))
          [SldCell.generatorDelta]
          = sldAppendCells (sldWireLayerOfArity vectorLengthPred)
              [SldCell.wire, SldCell.generatorDelta] := by
        rw [(sldWireLayerSplitsAtCount vectorLengthPred 1).symm, sldAppendCellsAssoc]
        exact rfl
      rw [firstLayerEq]
      have leftShape : sldPadLayersBelow 1
          (sldAppendLayers
            (sldPadLayersAbove vectorLengthPred
              (lstGadgetLayerList (firstColumn vectorLengthPred)))
            (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred firstColumn)))
          = sldAppendLayers
              (sldPadWindow vectorLengthPred 1
                (lstGadgetLayerList (firstColumn vectorLengthPred)))
              (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn)) := by
        rw [sldPadLayersBelowOfAppend, lstPadLayersBelowCompose,
          lstPadBelowOfPadAboveIsPadWindow]
      rw [leftShape, sldAppendLayersAssoc]
      have gadgetReachA : sldLayersTargetArityFrom 2
          (lstGadgetLayerList (firstColumn vectorLengthPred)) = 2 :=
        lstGadgetLayersReach (firstColumn vectorLengthPred)
      have walkWindow : sldLayersTargetArityFrom (vectorLengthPred + 3)
          (sldPadWindow vectorLengthPred 1
            (lstGadgetLayerList (firstColumn vectorLengthPred)))
          = vectorLengthPred + 3 := by
        have liftedReach := sldPadWindowTargetArityFrom vectorLengthPred 1
          (lstGadgetLayerList (firstColumn vectorLengthPred)) 2
        rw [gadgetReachA] at liftedReach
        exact liftedReach
      have blocksSlideTogether : SldAreConvertibleLayers (vectorLengthPred + 1 + 1)
          (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
              [SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers
                (sldPadWindow vectorLengthPred 1
                  (lstGadgetLayerList (firstColumn vectorLengthPred)))
                (sldAppendLayers
                  (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
                  (sldAppendLayers
                    (sldPadLayersAbove vectorLengthPred
                      (lstGadgetLayerList (secondColumn vectorLengthPred)))
                    (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred secondColumn)))))
          (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
              [SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers
                (sldPadWindow vectorLengthPred 1
                  (lstGadgetLayerList (firstColumn vectorLengthPred)))
                (sldAppendLayers
                  (sldPadLayersAbove (vectorLengthPred + 1)
                    (lstGadgetLayerList (secondColumn vectorLengthPred)))
                  (sldAppendLayers
                    (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
                    (sldPadLayersBelow 1
                      (lstFanLayerList vectorLengthPred secondColumn))))) := by
        have slideInstance := sldBlockSlidesDownPastBlock
          (lstFanLayerList vectorLengthPred firstColumn) (vectorLengthPred + 1)
          (lstFanLayersAreComposable vectorLengthPred firstColumn)
          (lstGadgetLayerList (secondColumn vectorLengthPred)) 2
          (lstGadgetLayersAreComposable (secondColumn vectorLengthPred))
          (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred secondColumn))
        rw [lstFanLayersReach, lstGadgetLayersReach] at slideInstance
        refine SldAreConvertibleLayers.underLayerPrefix (vectorLengthPred + 1 + 1)
          (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
            [SldCell.wire, SldCell.generatorDelta]) ?_
        have contextTarget : sldLayerTargetArity
            (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
              [SldCell.wire, SldCell.generatorDelta]) = vectorLengthPred + 3 := by
          rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
          exact rfl
        rw [contextTarget]
        refine sldConvUnderPrefixList
          (sldPadWindow vectorLengthPred 1
            (lstGadgetLayerList (firstColumn vectorLengthPred)))
          (vectorLengthPred + 3) _ _ ?_
        rw [walkWindow]
        exact slideInstance
      have gadgetsFuseWithSuffix : SldAreConvertibleLayers (vectorLengthPred + 1 + 1)
          (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
              [SldCell.wire, SldCell.generatorDelta]
            :: sldAppendLayers
                (sldPadWindow vectorLengthPred 1
                  (lstGadgetLayerList (firstColumn vectorLengthPred)))
                (sldAppendLayers
                  (sldPadLayersAbove (vectorLengthPred + 1)
                    (lstGadgetLayerList (secondColumn vectorLengthPred)))
                  (sldAppendLayers
                    (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
                    (sldPadLayersBelow 1
                      (lstFanLayerList vectorLengthPred secondColumn)))))
          (sldAppendLayers
            (sldPadLayersAbove vectorLengthPred
              (lstGadgetLayerList
                (firstColumn vectorLengthPred + secondColumn vectorLengthPred)))
            (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                [SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers
                  (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
                  (sldPadLayersBelow 1
                    (lstFanLayerList vectorLengthPred secondColumn)))) := by
        have paddedFusion := sldConvPadsAbove
          (lcoGadgetsFuseOverCopy (firstColumn vectorLengthPred)
            (secondColumn vectorLengthPred)) vectorLengthPred
        rw [show sldPadLayersAbove vectorLengthPred
              ([SldCell.wire, SldCell.generatorDelta]
                :: sldAppendLayers
                    (sldPadLayersBelow 1
                      (lstGadgetLayerList (firstColumn vectorLengthPred)))
                    (sldPadLayersAbove 1
                      (lstGadgetLayerList (secondColumn vectorLengthPred))))
            = sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                [SldCell.wire, SldCell.generatorDelta]
              :: sldPadLayersAbove vectorLengthPred
                  (sldAppendLayers
                    (sldPadLayersBelow 1
                      (lstGadgetLayerList (firstColumn vectorLengthPred)))
                    (sldPadLayersAbove 1
                      (lstGadgetLayerList (secondColumn vectorLengthPred)))) from rfl,
          sldPadLayersAboveOfAppend, lstPadAboveOfPadBelowIsPadWindow,
          lstPadLayersAboveCompose, sldPadLayersAboveOfAppend] at paddedFusion
        have withSuffix := sldConvAppendsSuffix paddedFusion
          (sldAppendLayers
            (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
            (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred secondColumn)))
        rw [show sldAppendLayers
              (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                  [SldCell.wire, SldCell.generatorDelta]
                :: sldAppendLayers
                    (sldPadWindow vectorLengthPred 1
                      (lstGadgetLayerList (firstColumn vectorLengthPred)))
                    (sldPadLayersAbove (vectorLengthPred + 1)
                      (lstGadgetLayerList (secondColumn vectorLengthPred))))
              (sldAppendLayers
                (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
                (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred secondColumn)))
            = sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                [SldCell.wire, SldCell.generatorDelta]
              :: sldAppendLayers
                  (sldAppendLayers
                    (sldPadWindow vectorLengthPred 1
                      (lstGadgetLayerList (firstColumn vectorLengthPred)))
                    (sldPadLayersAbove (vectorLengthPred + 1)
                      (lstGadgetLayerList (secondColumn vectorLengthPred))))
                  (sldAppendLayers
                    (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
                    (sldPadLayersBelow 1
                      (lstFanLayerList vectorLengthPred secondColumn))) from rfl,
          sldAppendLayersAssoc,
          show sldAppendLayers
              (sldAppendLayers
                (sldPadLayersAbove vectorLengthPred
                  (lstGadgetLayerList
                    (firstColumn vectorLengthPred + secondColumn vectorLengthPred)))
                (sldPadLayersAbove vectorLengthPred
                  [[SldCell.generatorDelta, SldCell.wire]]))
              (sldAppendLayers
                (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
                (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred secondColumn)))
            = sldAppendLayers
                (sldPadLayersAbove vectorLengthPred
                  (lstGadgetLayerList
                    (firstColumn vectorLengthPred + secondColumn vectorLengthPred)))
                (sldAppendLayers
                  (sldPadLayersAbove vectorLengthPred
                    [[SldCell.generatorDelta, SldCell.wire]])
                  (sldAppendLayers
                    (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
                    (sldPadLayersBelow 1
                      (lstFanLayerList vectorLengthPred secondColumn))))
            from sldAppendLayersAssoc _ _ _] at withSuffix
        exact withSuffix
      have recursionCloses : SldAreConvertibleLayers (vectorLengthPred + 1 + 1)
          (sldAppendLayers
            (sldPadLayersAbove vectorLengthPred
              (lstGadgetLayerList
                (firstColumn vectorLengthPred + secondColumn vectorLengthPred)))
            (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                [SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers
                  (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
                  (sldPadLayersBelow 1
                    (lstFanLayerList vectorLengthPred secondColumn))))
          (sldAppendLayers
            (sldPadLayersAbove vectorLengthPred
              (lstGadgetLayerList
                (firstColumn vectorLengthPred + secondColumn vectorLengthPred)))
            (sldPadLayersBelow 1
              (lstFanLayerList vectorLengthPred
                (fun mergeRow => firstColumn mergeRow + secondColumn mergeRow)))) := by
        have paddedRecursion := sldConvPadsBelow
          (lcoDeltaFanFusion vectorLengthPred firstColumn secondColumn) 1
        rw [show sldPadLayersBelow 1
              (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                  [SldCell.generatorDelta]
                :: sldAppendLayers
                    (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred firstColumn))
                    (lstFanLayerList vectorLengthPred secondColumn))
            = sldAppendCells
                (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                  [SldCell.generatorDelta])
                (sldWireLayerOfArity 1)
              :: sldPadLayersBelow 1
                  (sldAppendLayers
                    (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred firstColumn))
                    (lstFanLayerList vectorLengthPred secondColumn)) from rfl,
          sldAppendCellsAssoc, sldPadLayersBelowOfAppend,
          lstPadLayersBelowCompose] at paddedRecursion
        have aboveWalk : sldLayersTargetArityFrom (vectorLengthPred + 1 + 1)
            (sldPadLayersAbove vectorLengthPred
              (lstGadgetLayerList
                (firstColumn vectorLengthPred + secondColumn vectorLengthPred)))
            = vectorLengthPred + 2 := by
          have liftedReach := sldPadLayersAboveTargetArityFrom vectorLengthPred
            (lstGadgetLayerList
              (firstColumn vectorLengthPred + secondColumn vectorLengthPred)) 2
          rw [lstGadgetLayersReach] at liftedReach
          exact liftedReach
        refine sldConvUnderPrefixList
          (sldPadLayersAbove vectorLengthPred
            (lstGadgetLayerList
              (firstColumn vectorLengthPred + secondColumn vectorLengthPred)))
          (vectorLengthPred + 1 + 1) _ _ ?_
        rw [aboveWalk]
        exact paddedRecursion
      exact SldAreConvertibleLayers.fromTransitivity blocksSlideTogether
        (SldAreConvertibleLayers.fromTransitivity gadgetsFuseWithSuffix recursionCloses)

/-- THE DELTA FAN-FUSION STATEMENT IS INHABITED (ascription against the live Prop). -/
theorem lcoDeltaFanFusionHolds : lstDeltaFanFusionStatement :=
  fun vectorLength firstColumn secondColumn =>
    lcoDeltaFanFusion vectorLength firstColumn secondColumn


/-! ## Fires (SMALL denotes only, per the elaboration-cost discipline) -/

/-- MU-CORE FIRE (t = 1, constant column 2): the duplicated-fan conversion at the smallest
genuine fan. -/
theorem lcoMuCoreFire :
    SldAreConvertibleLayers 3
      (sldAppendCells (sldWireLayerOfArity 1) [SldCell.generatorMu]
        :: lstFanLayerList 1 (fun _sourceRow => 2))
      (sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 2)))
        (lstFanLayerList 1 (fun _sourceRow => 2))) :=
  lcoMuFanDuplication 1 (fun _sourceRow => 2)

/-- MU-CORE FIRE consumed through soundness: both sides denote the same matrix on the 1x3
rectangle — `acc + 2 * (x + y) = (acc + 2 * x) + 2 * y`. -/
theorem lcoMuCoreFireDenotesEqually :
    doEntriesAgreeUpTo 1 3
      (sldLayersDenote
        (sldAppendCells (sldWireLayerOfArity 1) [SldCell.generatorMu]
          :: lstFanLayerList 1 (fun _sourceRow => 2)))
      (sldLayersDenote
        (sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 2)))
          (lstFanLayerList 1 (fun _sourceRow => 2)))) = true :=
  sldConvertibleLayersDenoteAgreeUpTo lcoMuCoreFire 1

/-- SCALE-MU MATRIX PIN, kernel `rfl` at tower size two: the distributed side is the row
`[2, 2]` — both summands enter with scale 2. -/
theorem lcoScaleMuMatrixPin :
    (Nat.beq (sldLayersDenote ([SldCell.generatorMu] :: lstScaleLayerList 2) 0 0) 2
      && Nat.beq (sldLayersDenote ([SldCell.generatorMu] :: lstScaleLayerList 2) 0 1) 2)
      = true := rfl

/-- DELTA-CORE FIRE (t = 1, columns 1 and 2): the fused-fan conversion at the smallest
genuine fan pair. -/
theorem lcoDeltaCoreFire :
    SldAreConvertibleLayers 2
      (sldAppendCells (sldWireLayerOfArity 1) [SldCell.generatorDelta]
        :: sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 1)))
            (lstFanLayerList 1 (fun _sourceRow => 2)))
      (lstFanLayerList 1 (fun mergeRow => (fun _sourceRow => 1) mergeRow
        + (fun _sourceRow => 2) mergeRow)) :=
  lcoDeltaFanFusion 1 (fun _sourceRow => 1) (fun _sourceRow => 2)

/-- DELTA-CORE FIRE consumed through soundness: both sides denote the same matrix on the
1x2 rectangle — `(acc + 1 * x) + 2 * x = acc + 3 * x`. -/
theorem lcoDeltaCoreFireDenotesEqually :
    doEntriesAgreeUpTo 1 2
      (sldLayersDenote
        (sldAppendCells (sldWireLayerOfArity 1) [SldCell.generatorDelta]
          :: sldAppendLayers
              (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 1)))
              (lstFanLayerList 1 (fun _sourceRow => 2))))
      (sldLayersDenote (lstFanLayerList 1 (fun _sourceRow => 3))) = true :=
  sldConvertibleLayersDenoteAgreeUpTo
    (lcoDeltaFanFusion 1 (fun _sourceRow => 1) (fun _sourceRow => 2)) 1

/-- SCALE-FUSION MATRIX PIN, kernel `rfl`: the fused tower denotes `[3]` — `1 + 2 = 3` at
the matrix level. -/
theorem lcoScaleFusionMatrixPin :
    Nat.beq (sldLayersDenote (lstScaleLayerList 3) 0 0) 3 = true := rfl

/-- SCALE-MU FIRE consumed through soundness: `2 * (x + y) = 2 * x + 2 * y` at the matrix
level (1x2 rectangle). -/
theorem lcoScaleMuFireDenotesEqually :
    doEntriesAgreeUpTo 1 2
      (sldLayersDenote ([SldCell.generatorMu] :: lstScaleLayerList 2))
      (sldLayersDenote
        (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList 2))
          (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList 2))
            [[SldCell.generatorMu]]))) = true :=
  sldConvertibleLayersDenoteAgreeUpTo (lcoScaleTowerDistributesOverAdd 2) 1

/-- SCALE-FUSION FIRE consumed through soundness: `1 * x + 2 * x = 3 * x` at the matrix
level (1x1 rectangle). -/
theorem lcoScaleFusionFireDenotesEqually :
    doEntriesAgreeUpTo 1 1
      (sldLayersDenote
        ([SldCell.generatorDelta]
          :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList 1))
              (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList 2))
                [[SldCell.generatorMu]])))
      (sldLayersDenote (lstScaleLayerList 3)) = true :=
  sldConvertibleLayersDenoteAgreeUpTo (lcoScaleTowersFuseOverCopy 1 2) 1

/-- NEGATIVE CONTROL re-confirmed over the cores: scale towers of DISTINCT factors stay
non-convertible — the new conversion machinery did not collapse the semantics. -/
theorem lcoDistinctScaleTowersStayApart :
    SldAreConvertibleLayers 1 (lstScaleLayerList 1) (lstScaleLayerList 2) -> False :=
  sldNotConvertibleOfDistinctDenotes (lstScaleLayerList 1) (lstScaleLayerList 2) 1 rfl

/-! ## Markers and the honest ledger

* `lstMuFanDuplicationStatement` and `lstDeltaFanFusionStatement` are INHABITED above
  (`lcoMuFanDuplicationHolds` / `lcoDeltaFanFusionHolds`); the owner Bools in
  `StaircaseCompleteness` stay byte-intact false as frozen history — the inhabitants
  supersede them as content.
* `lstCrossingTwoFanSwapStatement` stays OPEN, not walled: ONE genuinely-different attack
  burned this round (documented below); the commission's wall threshold is three.
* `lstCanonicalReductionOverStrictLayersStatement` stays open — the assembly waits on the
  crossing core (the crossing-cell absorption is one of the six per-cell absorptions the
  layer induction dispatches over). -/

/-- Marker (true): the mu and delta bottom cores of the Lafont staircase are CLOSED — the
fan-duplication and fan-fusion statements are inhabited, on top of the full scale-level kit
(SCALE-TAU + mirror, SCALE-MU, SCALE-FUSION, GADGET-MU, GADGET-DELTA). -/
def fxLafontStaircase_hasMuDeltaFanCores : Bool := true

/-- Owner (false): the crossing two-fan-swap core is NOT proven in this round.  ATTACK
RECORD (1 of the 3 required for a wall): the direct braid alignment — expand both gadgets
through `lstGadgetLayerShape`, push the leading crossing through the copy layer (Ndelta),
slide it past the first scale window, exchange it past the merge, and align against the
target's crossing-emitting form.  CONFIGURATION REACHED: after five fires the left form is
`(w|delta|w) ; (w|w|w|delta) ; (w|w|tau|w) ; padWindow(1,3, scale a) ; ...` with THREE live
crossings mid-stream (the pushed crossing, the gadget-internal crossing of the first
gadget, and the second gadget's internal crossing) against the two-crossing target — the
crossing-count parity must be repaired through an M4/C4 fire that requires the two merge
spines to first meet on a shared five-strand window, and the alignment DIVERGED (each
naturality push re-emits a crossing on the other spine).  The conjugation reformulation
(`tau_h ; G_top(s) ; tau_h ~ tau_l ; G_bot(s) ; tau_l`) reduces the statement to a
rotation-conjugated two-gadget identity but does not dissolve the overlap.  Residual bill:
either (i) the one-gadget conjugation lemma plus the rho-conjugated middle identity
(estimated ~25 fires), or (iii) the scalar-content double induction. -/
def lcoCrossingTwoFanSwapProved : Bool := false

#eval decide (sldLayersDenote ([SldCell.generatorMu] :: lstScaleLayerList 2) 0 0 = 2)
#eval decide (sldLayersDenote ([SldCell.generatorMu] :: lstScaleLayerList 2) 0 1 = 2)
#eval decide (sldLayersDenote (lstScaleLayerList 3) 0 0 = 3)
#eval decide (doEntriesAgreeUpTo 1 1
  (sldLayersDenote (lstScaleLayerList 1)) (sldLayersDenote (lstScaleLayerList 2)) = false)
#eval decide (sldLayersAreComposableFrom 3
  (sldAppendCells (sldWireLayerOfArity 1) [SldCell.generatorMu]
    :: lstFanLayerList 1 (fun _sourceRow => 2)) = true)

end FX1Poly.Polygraph.Omega.LafontProp
