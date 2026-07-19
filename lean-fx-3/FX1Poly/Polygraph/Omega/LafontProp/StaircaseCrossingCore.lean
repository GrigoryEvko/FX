import FX1Poly.Polygraph.Omega.LafontProp.StaircaseCores

/-! # Polygraph/Omega/LafontProp/StaircaseCrossingCore — the crossing bottom core
(LAFONT-REPAIR stage 2 phase 4: THE THIRD FAN INTERACTION CLOSED — attack 2 fires)

The staircase left ONE open bottom core: `lstCrossingTwoFanSwapStatement` — two adjacent
column fans swap when their sources swap.  Attack 1 (direct braid alignment) burned last
round: pushing the crossing cell-by-cell re-emits a crossing on the other merge spine at
every naturality step and the count diverges (three live crossings against the two-crossing
target — see the record at `lcoCrossingTwoFanSwapProved`).  THIS file executes ATTACK 2, the
conjugation route, and CLOSES the core.  The insight that repairs the burn: never push the
leading crossing through gadget CELLS — push it through the WHOLE gadget window in one
derived lemma (the re-emitted crossings then cancel pairwise via S1 inside the window), and
reduce the two-gadget middle to a rotation-conjugated commutation of the swap-free gadget
halves.

## The ladder

* THE ONE-GADGET CONJUGATION (`lcxGadgetRidesConjugation`):
  `(w | tau) ; (gadget(s) | w) ; (w | tau) ~ (tau | w) ; (w | gadget(s)) ; (tau | w)` —
  the gadget rides through the crossing AS A UNIT.  Seven moves: Ndelta at pad one, the
  crossing slide below the scale window, the padded SCALE-TAU mirror, one disjoint
  exchange, the reroute kit, Yang-Baxter plus an S1 pair kill, and the two climbs back
  past the window and the copy.
* THE FAR-PREGADGET COMMUTATION (`lcxFarPregadgetsCommute`): two pregadgets merging INTO
  THE SAME accumulator from the two different sources commute — the rho-conjugated middle.
  Both orders parallelize onto ONE canonical form (`lcxParallelScaledMergeForm`: copy both
  sources, scale the copies on disjoint strands, double-merge, cross) by disjoint
  slides/exchanges and the two SCALE-TAU orientations; the residual order swap is the
  M1-M4-M1 lean of the left add tree, and the residual crossings die pairwise by S1.
* THE TWO-GADGET SWAP (`lcxGadgetPairSwapsAcrossCrossing`):
  `(w | tau) ; (gadget(a) | w) ; (w | gadget(b)) ~ (gadget(b) | w) ; (w | gadget(a)) ;
  (tau | w)` — assembled from the conjugation, the far commutation, Yang-Baxter, and S1.
* THE CORE (`lcxCrossingTwoFanSwap`): the fan-level source-climb induction in the exact
  mu/delta-core template — the freshly-peeled gadget pair converts by the padded two-gadget
  swap, the emitted below-crossing is consumed by the BELOW-PADDED INDUCTION HYPOTHESIS
  (the shorter two-fan swap), and the Godement block slides align the fan blocks.

## The flip

`lstCrossingTwoFanSwapStatement` is INHABITED (`lcxCrossingTwoFanSwapHolds`, ascription
against the live Prop verbatim).  The owner Bools in `StaircaseCompleteness` /
`StaircaseCores` stay byte-intact false as frozen history; the inhabitant supersedes them.
`fxLafontStaircase_hasCrossingCore` (here) records the close.  The full canonical
reduction (`lstCanonicalReductionOverStrictLayersStatement`) is NOT claimed by this file.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; audit twin with per-decl
`#assert_no_axioms` plus an independent `#print axioms` probe. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.LafontProp

/-! ## Chunk 1: pad bookkeeping — the gadget shapes and the scale-block boundary kit -/

/-- A window with an empty below pad is the plain above pad. -/
theorem lcxPadWindowWithZeroBelowIsPadAbove (padAboveCount : Nat) :
    (windowLayers : List SldLayer) ->
    sldPadWindow padAboveCount 0 windowLayers = sldPadLayersAbove padAboveCount windowLayers
  | [] => rfl
  | headLayer :: tailLayers => by
      show sldAppendCells (sldWireLayerOfArity padAboveCount)
          (sldAppendCells headLayer (sldWireLayerOfArity 0))
          :: sldPadWindow padAboveCount 0 tailLayers
        = sldAppendCells (sldWireLayerOfArity padAboveCount) headLayer
          :: sldPadLayersAbove padAboveCount tailLayers
      rw [show sldAppendCells headLayer (sldWireLayerOfArity 0) = headLayer from
          sldAppendCellsNilRightIsSelf headLayer,
        lcxPadWindowWithZeroBelowIsPadAbove padAboveCount tailLayers]

/-- Below-padded gadget, explicit layer shape. -/
theorem lcxGadgetPadBelowShape (scaleFactor : Nat) :
    sldPadLayersBelow 1 (lstGadgetLayerList scaleFactor)
      = [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire] :: []) := by
  rw [lstGadgetLayerShape, sldPadLayersBelowOfAppend, sldPadLayersBelowOfAppend,
    sldPadLayersBelowOfPadWindow]
  rfl

/-- Above-padded gadget, explicit layer shape. -/
theorem lcxGadgetPadAboveShape (scaleFactor : Nat) :
    sldPadLayersAbove 1 (lstGadgetLayerList scaleFactor)
      = [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: []) := by
  rw [lstGadgetLayerShape, sldPadLayersAboveOfAppend, sldPadLayersAboveOfAppend,
    sldPadLayersAboveOfPadWindow]
  rfl

/-- The above-padded scale block reaches two strands from two. -/
theorem lcxScaleAboveBlockReach (scaleFactor : Nat) :
    sldLayersTargetArityFrom 2 (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor)) = 2 := by
  have liftedReach := sldPadLayersAboveTargetArityFrom 1 (lstScaleLayerList scaleFactor) 1
  rw [lstScaleLayersReach] at liftedReach
  exact liftedReach

/-- The above-padded scale block composes from two strands. -/
theorem lcxScaleAboveBlockComposable (scaleFactor : Nat) :
    sldLayersAreComposableFrom 2 (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
      = true :=
  sldPadLayersAboveAreComposableFrom 1 (lstScaleLayerList scaleFactor) 1
    (lstScaleLayersAreComposable scaleFactor)


/-- The (1,1)-windowed scale block reaches three strands from three. -/
theorem lcxScaleWindowBlockReach (scaleFactor : Nat) :
    sldLayersTargetArityFrom 3 (sldPadWindow 1 1 (lstScaleLayerList scaleFactor)) = 3 := by
  have liftedReach := sldPadWindowTargetArityFrom 1 1 (lstScaleLayerList scaleFactor) 1
  rw [lstScaleLayersReach] at liftedReach
  exact liftedReach

/-- The (1,1)-windowed scale block composes from three strands. -/
theorem lcxScaleWindowBlockComposable (scaleFactor : Nat) :
    sldLayersAreComposableFrom 3 (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
      = true :=
  sldPadWindowIsComposableFrom 1 1 (lstScaleLayerList scaleFactor) 1
    (lstScaleLayersAreComposable scaleFactor)

/-! ## Chunk 2: the generic window tools — slides past a scale window, and the two
padded SCALE-TAU orientations (the "whole window in one move" repair of the attack-1 burn) -/

/-- A layer living strictly BELOW a padded scale window slides up past it (the window's
below-pad book-keeps the sliding layer's arities). -/
theorem lcxLayerSlidesBelowScaleWindow (scaleFactor padAboveCount : Nat)
    (slidingLayer : SldLayer) (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers (padAboveCount + 1 + sldLayerSourceArity slidingLayer)
      (sldAppendCells (sldWireLayerOfArity (padAboveCount + 1)) slidingLayer
        :: sldAppendLayers
            (sldPadWindow padAboveCount (sldLayerTargetArity slidingLayer)
              (lstScaleLayerList scaleFactor)) suffixLayers)
      (sldAppendLayers
        (sldPadWindow padAboveCount (sldLayerSourceArity slidingLayer)
          (lstScaleLayerList scaleFactor))
        (sldAppendCells (sldWireLayerOfArity (padAboveCount + 1)) slidingLayer
          :: suffixLayers)) := by
  have blockComposable : sldLayersAreComposableFrom (padAboveCount + 1)
      (sldPadLayersAbove padAboveCount (lstScaleLayerList scaleFactor)) = true :=
    sldPadLayersAboveAreComposableFrom padAboveCount (lstScaleLayerList scaleFactor) 1
      (lstScaleLayersAreComposable scaleFactor)
  have blockReach : sldLayersTargetArityFrom (padAboveCount + 1)
      (sldPadLayersAbove padAboveCount (lstScaleLayerList scaleFactor))
      = padAboveCount + 1 := by
    have liftedReach := sldPadLayersAboveTargetArityFrom padAboveCount
      (lstScaleLayerList scaleFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have slideInstance := sldLowerLayerSlidesDownPastBlock slidingLayer
    (sldPadLayersAbove padAboveCount (lstScaleLayerList scaleFactor)) (padAboveCount + 1)
    blockComposable suffixLayers
  rw [blockReach,
    lstPadBelowOfPadAboveIsPadWindow padAboveCount (sldLayerTargetArity slidingLayer),
    lstPadBelowOfPadAboveIsPadWindow padAboveCount (sldLayerSourceArity slidingLayer)]
    at slideInstance
  exact slideInstance

/-- A layer living strictly ABOVE a padded scale window slides down past it. -/
theorem lcxLayerSlidesAboveScaleWindow (scaleFactor padBelowCount : Nat)
    (slidingLayer : SldLayer) (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers (sldLayerSourceArity slidingLayer + (1 + padBelowCount))
      (sldAppendCells slidingLayer (sldWireLayerOfArity (1 + padBelowCount))
        :: sldAppendLayers
            (sldPadWindow (sldLayerTargetArity slidingLayer) padBelowCount
              (lstScaleLayerList scaleFactor)) suffixLayers)
      (sldAppendLayers
        (sldPadWindow (sldLayerSourceArity slidingLayer) padBelowCount
          (lstScaleLayerList scaleFactor))
        (sldAppendCells slidingLayer (sldWireLayerOfArity (1 + padBelowCount))
          :: suffixLayers)) := by
  have blockComposable : sldLayersAreComposableFrom (1 + padBelowCount)
      (sldPadLayersBelow padBelowCount (lstScaleLayerList scaleFactor)) = true :=
    sldPadLayersBelowAreComposableFrom padBelowCount (lstScaleLayerList scaleFactor) 1
      (lstScaleLayersAreComposable scaleFactor)
  have blockReach : sldLayersTargetArityFrom (1 + padBelowCount)
      (sldPadLayersBelow padBelowCount (lstScaleLayerList scaleFactor))
      = 1 + padBelowCount := by
    have liftedReach := sldPadLayersBelowTargetArityFrom padBelowCount
      (lstScaleLayerList scaleFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have slideInstance := sldUpperLayerSlidesDownPastBlock slidingLayer
    (sldPadLayersBelow padBelowCount (lstScaleLayerList scaleFactor)) (1 + padBelowCount)
    blockComposable suffixLayers
  rw [blockReach,
    lstPadAboveOfPadBelowIsPadWindow (sldLayerTargetArity slidingLayer) padBelowCount,
    lstPadAboveOfPadBelowIsPadWindow (sldLayerSourceArity slidingLayer) padBelowCount]
    at slideInstance
  exact slideInstance

/-- PADDED SCALE-TAU, mirror orientation: a crossing FOLLOWED by the scale tower on its
upper strand converts to the tower on the lower strand followed by the crossing — the tower
window moves one strand deeper.  All pads, with suffix. -/
theorem lcxCrossingPushesScaleDeeper (scaleFactor padAboveCount padBelowCount : Nat)
    (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers (padAboveCount + (2 + padBelowCount))
      (sldPadLayer padAboveCount padBelowCount [SldCell.crossing]
        :: sldAppendLayers
            (sldPadWindow padAboveCount (1 + padBelowCount) (lstScaleLayerList scaleFactor))
            suffixLayers)
      (sldAppendLayers
        (sldPadWindow (padAboveCount + 1) padBelowCount (lstScaleLayerList scaleFactor))
        (sldPadLayer padAboveCount padBelowCount [SldCell.crossing] :: suffixLayers)) := by
  have basePadded := lcoConvPadsWindow (lcoSwapDescendsIntoScaleTower scaleFactor)
    padAboveCount padBelowCount
  rw [show sldPadWindow padAboveCount padBelowCount
        ([SldCell.crossing] :: sldPadLayersBelow 1 (lstScaleLayerList scaleFactor))
      = sldPadLayer padAboveCount padBelowCount [SldCell.crossing]
        :: sldPadWindow padAboveCount padBelowCount
            (sldPadLayersBelow 1 (lstScaleLayerList scaleFactor)) from rfl,
    lcoPadWindowOfPadLayersBelow, lcoPadWindowOfAppendLayers,
    lcoPadWindowOfPadLayersAbove] at basePadded
  have withSuffix := sldConvAppendsSuffix basePadded suffixLayers
  rw [sldAppendLayersAssoc] at withSuffix
  exact withSuffix

/-- PADDED SCALE-TAU, direct orientation: the scale tower on the upper strand followed by a
crossing converts to the crossing followed by the tower one strand deeper.  All pads, with
suffix. -/
theorem lcxScaleSurfacesAcrossCrossing (scaleFactor padAboveCount padBelowCount : Nat)
    (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers (padAboveCount + (2 + padBelowCount))
      (sldAppendLayers
        (sldPadWindow padAboveCount (1 + padBelowCount) (lstScaleLayerList scaleFactor))
        (sldPadLayer padAboveCount padBelowCount [SldCell.crossing] :: suffixLayers))
      (sldPadLayer padAboveCount padBelowCount [SldCell.crossing]
        :: sldAppendLayers
            (sldPadWindow (padAboveCount + 1) padBelowCount (lstScaleLayerList scaleFactor))
            suffixLayers) := by
  have basePadded := lcoConvPadsWindow (lcoScaleTowerCrossesDown scaleFactor)
    padAboveCount padBelowCount
  rw [lcoPadWindowOfAppendLayers, lcoPadWindowOfPadLayersBelow,
    show sldPadWindow padAboveCount padBelowCount
        ([SldCell.crossing] :: sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
      = sldPadLayer padAboveCount padBelowCount [SldCell.crossing]
        :: sldPadWindow padAboveCount padBelowCount
            (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor)) from rfl,
    lcoPadWindowOfPadLayersAbove] at basePadded
  have withSuffix := sldConvAppendsSuffix basePadded suffixLayers
  rw [sldAppendLayersAssoc] at withSuffix
  exact withSuffix

/-! ## Chunk 3: THE ONE-GADGET CONJUGATION — the gadget rides through the crossing as a
unit; the re-emitted crossings cancel pairwise (S1/Yang-Baxter) INSIDE the window -/

/-- The reach of the copy-then-window prefix used to embed conversions behind the rotated
scale window. -/
theorem lcxCopyThenRotatedWindowReach (scaleFactor : Nat) :
    sldLayersTargetArityFrom 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldPadWindow 2 1 (lstScaleLayerList scaleFactor)) = 4 := by
  show sldLayersTargetArityFrom 4 (sldPadWindow 2 1 (lstScaleLayerList scaleFactor)) = 4
  have liftedReach := sldPadWindowTargetArityFrom 2 1 (lstScaleLayerList scaleFactor) 1
  rw [lstScaleLayersReach] at liftedReach
  exact liftedReach

/-- THE ONE-GADGET CONJUGATION: `(w | tau) ; (gadget(s) | w) ; (w | tau) ~
(tau | w) ; (w | gadget(s)) ; (tau | w)` — the whole gadget window rides through the
crossing as a unit.  The derivation pushes the crossing through the copy (Ndelta), slides
one emitted crossing below the scale window, rotates the window by the padded SCALE-TAU
mirror, exchanges past the merge, fires the reroute kit, kills the crossing surplus by
Yang-Baxter plus an S1 pair, and climbs the residual crossing back out. -/
theorem lcxGadgetRidesConjugation (scaleFactor : Nat) :
    SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: sldAppendLayers (sldPadLayersBelow 1 (lstGadgetLayerList scaleFactor))
            [[SldCell.wire, SldCell.crossing]])
      ([SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadLayersAbove 1 (lstGadgetLayerList scaleFactor))
            [[SldCell.crossing, SldCell.wire]]) := by
  rw [lcxGadgetPadBelowShape, lcxGadgetPadAboveShape]
  show SldAreConvertibleLayers 3
    ([SldCell.wire, SldCell.crossing]
      :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
      :: sldAppendLayers
          (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire] :: []))
          [[SldCell.wire, SldCell.crossing]])
    ([SldCell.crossing, SldCell.wire]
      :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
      :: sldAppendLayers
          (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: []))
          [[SldCell.crossing, SldCell.wire]])
  rw [sldAppendLayersAssoc (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.crossing, SldCell.wire] :: []) [[SldCell.wire, SldCell.crossing]],
    sldAppendLayersAssoc (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
      ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: []) [[SldCell.crossing, SldCell.wire]]]
  show SldAreConvertibleLayers 3
    ([SldCell.wire, SldCell.crossing]
      :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
      :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
          ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.crossing, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing] :: []))
    ([SldCell.crossing, SldCell.wire]
      :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
      :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
          ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing]
            :: [SldCell.crossing, SldCell.wire] :: []))
  -- Move 1 (Ndelta at pad one): the crossing pushes through the copy, emitting two.
  have copyPushes : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: []))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: [])) :=
    SldAreConvertibleLayers.fromCopyPastSwapRow 1 0
      (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
        ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: [SldCell.crossing, SldCell.wire]
          :: [SldCell.wire, SldCell.crossing] :: []))
  -- Move 2: the deeper emitted crossing slides below the scale window.
  have lowerTauSlides : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: []))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: [])) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.wire, SldCell.generatorDelta],
        [SldCell.wire, SldCell.crossing, SldCell.wire]] 3 _ _
      (lcxLayerSlidesBelowScaleWindow scaleFactor 1 [SldCell.crossing]
        ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: [SldCell.crossing, SldCell.wire]
          :: [SldCell.wire, SldCell.crossing] :: []))
  -- Move 3 (padded SCALE-TAU mirror): the remaining crossing rotates the scale window.
  have windowRotates : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: []))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: [])) :=
    SldAreConvertibleLayers.underLayerPrefix 3
      [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
      (lcxCrossingPushesScaleDeeper scaleFactor 1 1
        ([SldCell.wire, SldCell.wire, SldCell.crossing]
          :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: [SldCell.crossing, SldCell.wire]
          :: [SldCell.wire, SldCell.crossing] :: []))
  -- Move 4: the deep crossing exchanges past the merge.
  have addTauExchanges : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: []))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.crossing, SldCell.wire]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: [])) := by
    refine sldConvUnderPrefixList
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldPadWindow 2 1 (lstScaleLayerList scaleFactor)) 3 _ _ ?_
    rw [lcxCopyThenRotatedWindowReach]
    exact SldAreConvertibleLayers.underLayerPrefix 4
      [SldCell.wire, SldCell.crossing, SldCell.wire]
      (SldAreConvertibleLayers.fromSymmetry
        (sldDisjointLayersExchange [SldCell.generatorMu] [SldCell.crossing]
          ([SldCell.crossing, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing] :: [])))
  -- Move 5 (the reroute kit): swap-then-upper-add reroutes through the lower add.
  have addReroutes : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.crossing, SldCell.wire]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: []))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.crossing, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: [])) := by
    refine sldConvUnderPrefixList
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldPadWindow 2 1 (lstScaleLayerList scaleFactor)) 3 _ _ ?_
    rw [lcxCopyThenRotatedWindowReach]
    have basePadded := lcoConvPadsWindow (lcoSwapThenUpperAddReroutes []) 0 1
    have withSuffix := sldConvAppendsSuffix basePadded
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: [])
    exact withSuffix
  -- Move 6 (Yang-Baxter): the leading three of the four-crossing tail braid over.
  have braidRealigns : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.crossing, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: []))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.crossing, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.crossing] :: [])) := by
    refine sldConvUnderPrefixList
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldPadWindow 2 1 (lstScaleLayerList scaleFactor)) 3 _ _ ?_
    rw [lcxCopyThenRotatedWindowReach]
    exact sldConvUnderPrefixList
      [[SldCell.crossing, SldCell.wire, SldCell.wire],
        [SldCell.wire, SldCell.generatorMu, SldCell.wire]] 4 _ _
      (SldAreConvertibleLayers.fromSwapYangBaxterRow 0 0
        ([SldCell.wire, SldCell.crossing] :: []))
  -- Move 7 (S1): the trailing crossing pair dies.
  have crossingPairDies : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.crossing, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.crossing] :: []))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.crossing, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.crossing, SldCell.wire] :: [])) := by
    refine sldConvUnderPrefixList
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldPadWindow 2 1 (lstScaleLayerList scaleFactor)) 3 _ _ ?_
    rw [lcxCopyThenRotatedWindowReach]
    exact sldConvUnderPrefixList
      [[SldCell.crossing, SldCell.wire, SldCell.wire],
        [SldCell.wire, SldCell.generatorMu, SldCell.wire],
        [SldCell.wire, SldCell.crossing],
        [SldCell.crossing, SldCell.wire]] 4 _ _
      (lcoTauPairDiesUnderWire [])
  -- Move 8: the surviving top crossing climbs back above the scale window.
  have upperTauClimbs : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.crossing, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.crossing, SldCell.wire] :: []))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.crossing, SldCell.wire] :: [])) :=
    SldAreConvertibleLayers.underLayerPrefix 3
      [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
      (SldAreConvertibleLayers.fromSymmetry
        (lcxLayerSlidesAboveScaleWindow scaleFactor 1 [SldCell.crossing]
          ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing]
            :: [SldCell.crossing, SldCell.wire] :: [])))
  -- Move 9: the crossing exchanges past the copy — the conjugated form.
  have copyTauExchanges : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.crossing, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.crossing, SldCell.wire] :: []))
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.crossing, SldCell.wire] :: [])) :=
    SldAreConvertibleLayers.fromSymmetry
      (sldDisjointLayersExchange [SldCell.crossing] [SldCell.generatorDelta]
        (sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
          ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing]
            :: [SldCell.crossing, SldCell.wire] :: [])))
  exact SldAreConvertibleLayers.fromTransitivity copyPushes
    (SldAreConvertibleLayers.fromTransitivity lowerTauSlides
      (SldAreConvertibleLayers.fromTransitivity windowRotates
        (SldAreConvertibleLayers.fromTransitivity addTauExchanges
          (SldAreConvertibleLayers.fromTransitivity addReroutes
            (SldAreConvertibleLayers.fromTransitivity braidRealigns
              (SldAreConvertibleLayers.fromTransitivity crossingPairDies
                (SldAreConvertibleLayers.fromTransitivity upperTauClimbs
                  copyTauExchanges)))))))

/-! ## Chunk 4: THE FAR-PREGADGET COMMUTATION — two pregadgets merging into the same
accumulator from different sources commute (the rho-conjugated middle of the two-fan swap) -/

/-- Window reach: `(1,2)` scale window keeps boundary four. -/
theorem lcxWindowOneTwoReachFromFour (scaleFactor : Nat) :
    sldLayersTargetArityFrom 4 (sldPadWindow 1 2 (lstScaleLayerList scaleFactor)) = 4 := by
  have liftedReach := sldPadWindowTargetArityFrom 1 2 (lstScaleLayerList scaleFactor) 1
  rw [lstScaleLayersReach] at liftedReach
  exact liftedReach

/-- Window reach: `(1,3)` scale window keeps boundary five. -/
theorem lcxWindowOneThreeReachFromFive (scaleFactor : Nat) :
    sldLayersTargetArityFrom 5 (sldPadWindow 1 3 (lstScaleLayerList scaleFactor)) = 5 := by
  have liftedReach := sldPadWindowTargetArityFrom 1 3 (lstScaleLayerList scaleFactor) 1
  rw [lstScaleLayersReach] at liftedReach
  exact liftedReach

/-- Window reach: `(2,2)` scale window keeps boundary five. -/
theorem lcxWindowTwoTwoReachFromFive (scaleFactor : Nat) :
    sldLayersTargetArityFrom 5 (sldPadWindow 2 2 (lstScaleLayerList scaleFactor)) = 5 := by
  have liftedReach := sldPadWindowTargetArityFrom 2 2 (lstScaleLayerList scaleFactor) 1
  rw [lstScaleLayersReach] at liftedReach
  exact liftedReach

/-- Window reach: `(3,1)` scale window keeps boundary five. -/
theorem lcxWindowThreeOneReachFromFive (scaleFactor : Nat) :
    sldLayersTargetArityFrom 5 (sldPadWindow 3 1 (lstScaleLayerList scaleFactor)) = 5 := by
  have liftedReach := sldPadWindowTargetArityFrom 3 1 (lstScaleLayerList scaleFactor) 1
  rw [lstScaleLayersReach] at liftedReach
  exact liftedReach

/-- THE CANONICAL PARALLEL FORM both far-merge orders reduce to: copy both sources, scale
the two inner copies on DISJOINT strands, cross once, then double-merge into the
accumulator. -/
def lcxParallelScaledMergeForm (firstFactor secondFactor : Nat) : List SldLayer :=
  [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
    :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
    :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
        (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
          ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))

/-- Conversions behind the two disjoint scale windows of the parallel form lift under the
window pair. -/
theorem lcxConvBehindWindowPair (firstFactor secondFactor : Nat)
    {tailLeft tailRight : List SldLayer}
    (innerConvertible : SldAreConvertibleLayers 5 tailLeft tailRight) :
    SldAreConvertibleLayers 5
      (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
        (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor)) tailLeft))
      (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
        (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor)) tailRight)) := by
  refine sldConvUnderPrefixList (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) 5 _ _ ?_
  rw [lcxWindowOneThreeReachFromFive]
  refine sldConvUnderPrefixList (sldPadWindow 3 1 (lstScaleLayerList secondFactor)) 5 _ _ ?_
  rw [lcxWindowThreeOneReachFromFive]
  exact innerConvertible

/-- LEFT SPINE: merge the first source, then the far-conjugated second merge — reduces to
the canonical parallel form. -/
theorem lcxFarPregadgetsLeftSpine (firstFactor secondFactor : Nat) :
    SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: [])))
      (lcxParallelScaledMergeForm firstFactor secondFactor) := by
  -- Move 1: the middle crossing exchanges past the first merge.
  have midTauExchanges : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: []))) := by
    refine SldAreConvertibleLayers.underLayerPrefix 3
      [SldCell.wire, SldCell.generatorDelta, SldCell.wire] ?_
    refine sldConvUnderPrefixList (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) 4 _ _ ?_
    rw [lcxWindowOneTwoReachFromFour]
    exact sldDisjointLayersExchange [SldCell.generatorMu] [SldCell.crossing]
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: []))
  -- Move 2: the second copy exchanges past the first merge.
  have copyMuExchanges : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: []))) := by
    refine SldAreConvertibleLayers.underLayerPrefix 3
      [SldCell.wire, SldCell.generatorDelta, SldCell.wire] ?_
    refine sldConvUnderPrefixList (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) 4 _ _ ?_
    rw [lcxWindowOneTwoReachFromFour]
    exact SldAreConvertibleLayers.underLayerPrefix 4
      [SldCell.wire, SldCell.wire, SldCell.crossing]
      (sldDisjointLayersExchange [SldCell.generatorMu]
        [SldCell.generatorDelta, SldCell.wire]
        (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
          ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing] :: [])))
  -- Move 3: the first merge slides below the second scale window.
  have muSlidesBelowSecondWindow : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                    :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: []))) := by
    refine SldAreConvertibleLayers.underLayerPrefix 3
      [SldCell.wire, SldCell.generatorDelta, SldCell.wire] ?_
    refine sldConvUnderPrefixList (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) 4 _ _ ?_
    rw [lcxWindowOneTwoReachFromFour]
    exact sldConvUnderPrefixList
      [[SldCell.wire, SldCell.wire, SldCell.crossing],
        [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]] 4 _ _
      (lcxLayerSlidesAboveScaleWindow secondFactor 2 [SldCell.generatorMu]
        ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: [SldCell.wire, SldCell.crossing] :: []))
  -- Move 4: the emitted crossing climbs above the first scale window.
  have tauClimbsAboveFirstWindow : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                    :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                    :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: []))) :=
    SldAreConvertibleLayers.underLayerPrefix 3
      [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
      (SldAreConvertibleLayers.fromSymmetry
        (lcxLayerSlidesBelowScaleWindow firstFactor 1 [SldCell.crossing]
          ([SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
                ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                  :: [SldCell.wire, SldCell.crossing] :: []))))
  -- Move 5: the second copy climbs above the first scale window.
  have copyClimbsAboveFirstWindow : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                    :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing] :: []))) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.generatorDelta, SldCell.wire],
        [SldCell.wire, SldCell.wire, SldCell.crossing]] 3 _ _
      (SldAreConvertibleLayers.fromSymmetry
        (lcxLayerSlidesBelowScaleWindow firstFactor 1
          [SldCell.generatorDelta, SldCell.wire]
          (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: []))))
  -- Move 6 (Ndelta at pad two): the crossing pushes through the second copy.
  have copyPushesDeep : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing] :: []))) :=
    SldAreConvertibleLayers.underLayerPrefix 3
      [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
      (SldAreConvertibleLayers.fromCopyPastSwapRow 2 0
        (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
          (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: []))))
  -- Move 7: the deepest emitted crossing descends below BOTH windows.
  have deepTauDescendsFirst : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
                ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                  :: [SldCell.wire, SldCell.crossing] :: []))) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.generatorDelta, SldCell.wire],
        [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta],
        [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]] 3 _ _
      (lcxLayerSlidesBelowScaleWindow firstFactor 1 [SldCell.wire, SldCell.crossing]
        (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
          ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing] :: [])))
  have deepTauDescendsSecond : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
                ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                  :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing] :: []))) := by
    refine sldConvUnderPrefixList
      [[SldCell.wire, SldCell.generatorDelta, SldCell.wire],
        [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta],
        [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]] 3 _ _ ?_
    refine sldConvUnderPrefixList (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) 5 _ _ ?_
    rw [lcxWindowOneThreeReachFromFive]
    exact lcxLayerSlidesBelowScaleWindow secondFactor 2 [SldCell.crossing]
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: [])
  -- Move 8: the middle crossing descends below the first window.
  have midTauDescends : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
                ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                  :: [SldCell.wire, SldCell.crossing] :: []))) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.generatorDelta, SldCell.wire],
        [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]] 3 _ _
      (lcxLayerSlidesBelowScaleWindow firstFactor 1 [SldCell.crossing, SldCell.wire]
        (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
          ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing] :: [])))
  -- Move 9 (padded SCALE-TAU mirror): the crossing pushes the second window one deeper.
  have secondWindowRotates : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
                ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                  :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing] :: []))) := by
    refine sldConvUnderPrefixList
      [[SldCell.wire, SldCell.generatorDelta, SldCell.wire],
        [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]] 3 _ _ ?_
    refine sldConvUnderPrefixList (sldPadWindow 1 3 (lstScaleLayerList firstFactor)) 5 _ _ ?_
    rw [lcxWindowOneThreeReachFromFive]
    exact lcxCrossingPushesScaleDeeper secondFactor 2 1
      ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: [])
  -- Move 10: the two copies exchange into canonical order.
  have copiesExchange : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing] :: []))) :=
    sldDisjointLayersExchange [SldCell.wire, SldCell.generatorDelta]
      [SldCell.generatorDelta]
      (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
        (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
          ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
            :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
            :: [SldCell.wire, SldCell.crossing] :: [])))
  -- Move 11 (the tail lean): the surplus crossing walks to the end and dies on the pair.
  have deepTauMeetsFirstAdd : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: [])
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: []) :=
    SldAreConvertibleLayers.fromSymmetry
      (sldDisjointLayersExchange [SldCell.generatorMu, SldCell.wire] [SldCell.crossing]
        ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: [SldCell.wire, SldCell.crossing] :: []))
  have deepTauMeetsSecondAdd : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: [])
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.crossing] :: []) :=
    SldAreConvertibleLayers.fromTransitivity deepTauMeetsFirstAdd
      (SldAreConvertibleLayers.underLayerPrefix 5
        [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        (SldAreConvertibleLayers.fromSymmetry
          (sldDisjointLayersExchange [SldCell.generatorMu] [SldCell.crossing]
            ([SldCell.wire, SldCell.crossing] :: []))))
  have tailPairDies : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing] :: [])
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []) :=
    SldAreConvertibleLayers.fromTransitivity deepTauMeetsSecondAdd
      (sldConvUnderPrefixList
        [[SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire],
          [SldCell.generatorMu, SldCell.wire, SldCell.wire]] 5 _ _
        (lcoTauPairDiesUnderWire []))
  have tailLeans : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.wire, SldCell.wire, SldCell.crossing]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing] :: [])))
      (lcxParallelScaledMergeForm firstFactor secondFactor) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.wire, SldCell.generatorDelta],
        [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]] 3 _ _
      (lcxConvBehindWindowPair firstFactor secondFactor
        (SldAreConvertibleLayers.underLayerPrefix 5
          [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
          tailPairDies))
  exact SldAreConvertibleLayers.fromTransitivity midTauExchanges
    (SldAreConvertibleLayers.fromTransitivity copyMuExchanges
      (SldAreConvertibleLayers.fromTransitivity muSlidesBelowSecondWindow
        (SldAreConvertibleLayers.fromTransitivity tauClimbsAboveFirstWindow
          (SldAreConvertibleLayers.fromTransitivity copyClimbsAboveFirstWindow
            (SldAreConvertibleLayers.fromTransitivity copyPushesDeep
              (SldAreConvertibleLayers.fromTransitivity deepTauDescendsFirst
                (SldAreConvertibleLayers.fromTransitivity deepTauDescendsSecond
                  (SldAreConvertibleLayers.fromTransitivity midTauDescends
                    (SldAreConvertibleLayers.fromTransitivity secondWindowRotates
                      (SldAreConvertibleLayers.fromTransitivity copiesExchange
                        tailLeans))))))))))

/-- RIGHT SPINE: the far-conjugated second merge first, then the first merge — reduces to
the SAME canonical parallel form (the leading crossing dies against the copy by Ndelta plus
S1; the order swap of the two merges is the M1-M4-M1 lean). -/
theorem lcxFarPregadgetsRightSpine (firstFactor secondFactor : Nat) :
    SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      (lcxParallelScaledMergeForm firstFactor secondFactor) := by
  -- Move 1: the middle crossing exchanges past the second-source merge.
  have midTauExchanges : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))) := by
    refine sldConvUnderPrefixList
      [[SldCell.wire, SldCell.crossing],
        [SldCell.wire, SldCell.generatorDelta, SldCell.wire]] 3 _ _ ?_
    refine sldConvUnderPrefixList (sldPadWindow 1 2 (lstScaleLayerList secondFactor)) 4 _ _ ?_
    rw [lcxWindowOneTwoReachFromFour]
    exact sldDisjointLayersExchange [SldCell.generatorMu] [SldCell.crossing]
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))
  -- Move 2: the first-source copy exchanges past the second-source merge.
  have copyMuExchanges : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))) := by
    refine sldConvUnderPrefixList
      [[SldCell.wire, SldCell.crossing],
        [SldCell.wire, SldCell.generatorDelta, SldCell.wire]] 3 _ _ ?_
    refine sldConvUnderPrefixList (sldPadWindow 1 2 (lstScaleLayerList secondFactor)) 4 _ _ ?_
    rw [lcxWindowOneTwoReachFromFour]
    exact SldAreConvertibleLayers.underLayerPrefix 4
      [SldCell.wire, SldCell.wire, SldCell.crossing]
      (sldDisjointLayersExchange [SldCell.generatorMu]
        [SldCell.generatorDelta, SldCell.wire]
        (sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
          ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
  -- Move 3: the second-source merge slides below the first scale window.
  have muSlidesBelowFirstWindow : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                    :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))) := by
    refine sldConvUnderPrefixList
      [[SldCell.wire, SldCell.crossing],
        [SldCell.wire, SldCell.generatorDelta, SldCell.wire]] 3 _ _ ?_
    refine sldConvUnderPrefixList (sldPadWindow 1 2 (lstScaleLayerList secondFactor)) 4 _ _ ?_
    rw [lcxWindowOneTwoReachFromFour]
    exact sldConvUnderPrefixList
      [[SldCell.wire, SldCell.wire, SldCell.crossing],
        [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]] 4 _ _
      (lcxLayerSlidesAboveScaleWindow firstFactor 2 [SldCell.generatorMu]
        ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))
  -- Move 4: the emitted crossing climbs above the second scale window.
  have tauClimbsAboveSecondWindow : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                    :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                    :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.crossing],
        [SldCell.wire, SldCell.generatorDelta, SldCell.wire]] 3 _ _
      (SldAreConvertibleLayers.fromSymmetry
        (lcxLayerSlidesBelowScaleWindow secondFactor 1 [SldCell.crossing]
          ([SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
            :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
                ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))))
  -- Move 5: the first-source copy climbs above the second scale window.
  have copyClimbsAboveSecondWindow : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                    :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList secondFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.crossing],
        [SldCell.wire, SldCell.generatorDelta, SldCell.wire],
        [SldCell.wire, SldCell.wire, SldCell.crossing]] 3 _ _
      (SldAreConvertibleLayers.fromSymmetry
        (lcxLayerSlidesBelowScaleWindow secondFactor 1
          [SldCell.generatorDelta, SldCell.wire]
          (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
              :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))))
  -- Move 6 (Ndelta at pad one): the LEADING crossing pushes through the second copy.
  have leadingCopyPushes : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList secondFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList secondFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))) :=
    SldAreConvertibleLayers.fromCopyPastSwapRow 1 0
      ([SldCell.wire, SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList secondFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
  -- Move 7 (S1): the emitted deep crossing annihilates the resident one.
  have deepPairDies : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList secondFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList secondFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.wire, SldCell.generatorDelta],
        [SldCell.wire, SldCell.crossing, SldCell.wire]] 3 _ _
      (SldAreConvertibleLayers.fromSwapInvolutionRow 2 0
        ([SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
          :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList secondFactor))
              (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
                ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))))
  -- Move 8 (mirror Ndelta, padded): the surviving crossing pushes through the first copy.
  have residualCopyPushes : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList secondFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList secondFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))) := by
    refine SldAreConvertibleLayers.underLayerPrefix 3
      [SldCell.wire, SldCell.wire, SldCell.generatorDelta] ?_
    have mirrorPadded := lcoConvPadsWindow
      (SldAreConvertibleLayers.fromSymmetry (lcoCopySlidesBelowParkedStrand [])) 1 1
    have mirrorWithSuffix := sldConvAppendsSuffix mirrorPadded
      (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList secondFactor))
        (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
          ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
    exact mirrorWithSuffix
  -- Move 9 (padded SCALE-TAU mirror): the lower crossing pushes the second window deeper.
  have secondWindowRotates : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList secondFactor))
            (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
              ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
            ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
                ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.wire, SldCell.generatorDelta],
        [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire],
        [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]] 3 _ _
      (lcxCrossingPushesScaleDeeper secondFactor 1 2
        (sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
          ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
  -- Move 10 (padded SCALE-TAU direct): the first window surfaces across the crossing.
  have firstWindowSurfaces : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
            ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList firstFactor))
                ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
            (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
              ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))) := by
    refine sldConvUnderPrefixList
      [[SldCell.wire, SldCell.wire, SldCell.generatorDelta],
        [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire],
        [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]] 3 _ _ ?_
    refine sldConvUnderPrefixList (sldPadWindow 2 2 (lstScaleLayerList secondFactor)) 5 _ _ ?_
    rw [lcxWindowTwoTwoReachFromFive]
    exact SldAreConvertibleLayers.fromSymmetry
      (lcxScaleSurfacesAcrossCrossing firstFactor 1 2
        ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
          :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))
  -- Move 11 (padded SCALE-TAU mirror): the upper crossing pushes the second window deeper.
  have secondWindowRotatesAgain : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 2 2 (lstScaleLayerList secondFactor))
            (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
              ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
                ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.wire, SldCell.generatorDelta],
        [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]] 3 _ _
      (lcxCrossingPushesScaleDeeper secondFactor 2 1
        (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
          ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
            :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
  -- Move 12: the upper crossing descends below the first window (disjoint).
  have upperTauDescends : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
            ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
                ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                  :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
            (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))) := by
    refine sldConvUnderPrefixList
      [[SldCell.wire, SldCell.wire, SldCell.generatorDelta],
        [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]] 3 _ _ ?_
    refine sldConvUnderPrefixList (sldPadWindow 3 1 (lstScaleLayerList secondFactor)) 5 _ _ ?_
    rw [lcxWindowThreeOneReachFromFive]
    exact lcxLayerSlidesBelowScaleWindow firstFactor 1 [SldCell.crossing, SldCell.wire]
      ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])
  -- Move 13: the two windows exchange into canonical order (Godement block slide).
  have windowsExchange : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
            (sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))) := by
    refine sldConvUnderPrefixList
      [[SldCell.wire, SldCell.wire, SldCell.generatorDelta],
        [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]] 3 _ _ ?_
    have slideInstance := sldBlockSlidesDownPastBlock
      (sldPadLayersAbove 1 (lstScaleLayerList firstFactor)) 2
      (lcxScaleAboveBlockComposable firstFactor)
      (sldPadWindow 1 1 (lstScaleLayerList secondFactor)) 3
      (lcxScaleWindowBlockComposable secondFactor)
      ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])
    rw [lcxScaleAboveBlockReach, lcxScaleWindowBlockReach,
      lstPadBelowOfPadAboveIsPadWindow 1 3,
      show sldPadLayersAbove 2 (sldPadWindow 1 1 (lstScaleLayerList secondFactor))
          = sldPadWindow 3 1 (lstScaleLayerList secondFactor) from
        sldPadLayersAboveOfPadWindow 2 1 1 (lstScaleLayerList secondFactor)]
      at slideInstance
    exact SldAreConvertibleLayers.fromSymmetry slideInstance
  -- Move 14 (the M1-M4-M1 lean): the residual crossing dies against the left add tree.
  have crossingDiesOnAddTree : SldAreConvertibleLayers 5
      ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])
      ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []) := by
    have treeLeans : SldAreConvertibleLayers 5
        ([SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
          :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])
        ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []) :=
      SldAreConvertibleLayers.fromAddAssociativityRow 0 2 []
    have commutativityFires : SldAreConvertibleLayers 5
        ([SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
          :: [SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])
        ([SldCell.wire, SldCell.generatorMu, SldCell.wire, SldCell.wire]
          :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []) :=
      SldAreConvertibleLayers.fromAddCommutativityRow 1 2
        ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])
    exact SldAreConvertibleLayers.fromTransitivity
      (SldAreConvertibleLayers.underLayerPrefix 5
        [SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire] treeLeans)
      (SldAreConvertibleLayers.fromTransitivity commutativityFires
        (SldAreConvertibleLayers.fromSymmetry treeLeans))
  have tailLeans : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 3 (lstScaleLayerList firstFactor))
            (sldAppendLayers (sldPadWindow 3 1 (lstScaleLayerList secondFactor))
              ([SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
                :: [SldCell.wire, SldCell.crossing, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire, SldCell.wire]
                :: [SldCell.generatorMu, SldCell.wire, SldCell.wire] :: [])))
      (lcxParallelScaledMergeForm firstFactor secondFactor) :=
    sldConvUnderPrefixList
      [[SldCell.wire, SldCell.wire, SldCell.generatorDelta],
        [SldCell.wire, SldCell.generatorDelta, SldCell.wire, SldCell.wire]] 3 _ _
      (lcxConvBehindWindowPair firstFactor secondFactor
        (SldAreConvertibleLayers.underLayerPrefix 5
          [SldCell.wire, SldCell.wire, SldCell.crossing, SldCell.wire]
          crossingDiesOnAddTree))
  exact SldAreConvertibleLayers.fromTransitivity midTauExchanges
    (SldAreConvertibleLayers.fromTransitivity copyMuExchanges
      (SldAreConvertibleLayers.fromTransitivity muSlidesBelowFirstWindow
        (SldAreConvertibleLayers.fromTransitivity tauClimbsAboveSecondWindow
          (SldAreConvertibleLayers.fromTransitivity copyClimbsAboveSecondWindow
            (SldAreConvertibleLayers.fromTransitivity leadingCopyPushes
              (SldAreConvertibleLayers.fromTransitivity deepPairDies
                (SldAreConvertibleLayers.fromTransitivity residualCopyPushes
                  (SldAreConvertibleLayers.fromTransitivity secondWindowRotates
                    (SldAreConvertibleLayers.fromTransitivity firstWindowSurfaces
                      (SldAreConvertibleLayers.fromTransitivity secondWindowRotatesAgain
                        (SldAreConvertibleLayers.fromTransitivity upperTauDescends
                          (SldAreConvertibleLayers.fromTransitivity windowsExchange
                            tailLeans))))))))))))

/-- THE FAR-PREGADGET COMMUTATION: merging the first source then the far-conjugated second
source converts to the two merges in the OPPOSITE order — both reduce to the canonical
parallel form. -/
theorem lcxFarPregadgetsCommute (firstFactor secondFactor : Nat) :
    SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire] :: []))) :=
  SldAreConvertibleLayers.fromTransitivity
    (lcxFarPregadgetsLeftSpine firstFactor secondFactor)
    (SldAreConvertibleLayers.fromSymmetry
      (lcxFarPregadgetsRightSpine firstFactor secondFactor))

/-! ## Chunk 5: THE TWO-GADGET SWAP — conjugate the first column, commute the far
pregadgets, kill the crossing surplus -/

/-- Cons-exposure of the layer-list append (rewrite normal form helper). -/
theorem lcxAppendLayersConsExposes (headLayer : SldLayer)
    (tailLayers extraLayers : List SldLayer) :
    sldAppendLayers (headLayer :: tailLayers) extraLayers
      = headLayer :: sldAppendLayers tailLayers extraLayers := rfl

/-- Nil-exposure of the layer-list append (rewrite normal form helper). -/
theorem lcxAppendLayersNilExposes (extraLayers : List SldLayer) :
    sldAppendLayers [] extraLayers = extraLayers := rfl

/-- Window reach: `(2,1)` scale window keeps boundary four. -/
theorem lcxWindowTwoOneReachFromFour (scaleFactor : Nat) :
    sldLayersTargetArityFrom 4 (sldPadWindow 2 1 (lstScaleLayerList scaleFactor)) = 4 := by
  have liftedReach := sldPadWindowTargetArityFrom 2 1 (lstScaleLayerList scaleFactor) 1
  rw [lstScaleLayersReach] at liftedReach
  exact liftedReach

/-- The above-padded gadget keeps boundary three. -/
theorem lcxGadgetAboveReach (scaleFactor : Nat) :
    sldLayersTargetArityFrom 3 (sldPadLayersAbove 1 (lstGadgetLayerList scaleFactor))
      = 3 := by
  have liftedReach := sldPadLayersAboveTargetArityFrom 1 (lstGadgetLayerList scaleFactor) 2
  rw [lstGadgetLayersReach] at liftedReach
  exact liftedReach

/-- The conjugation in fully-expanded shape (both sides through the gadget shape lemmas,
appends right-normalized). -/
theorem lcxGadgetRidesConjugationShaped (scaleFactor : Nat) :
    SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: []))
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.crossing, SldCell.wire] :: [])) := by
  have baseConjugation := lcxGadgetRidesConjugation scaleFactor
  rw [lcxGadgetPadBelowShape, lcxGadgetPadAboveShape] at baseConjugation
  simp only [lcxAppendLayersConsExposes, lcxAppendLayersNilExposes, sldAppendLayersAssoc]
    at baseConjugation
  exact baseConjugation

/-- The upper gadget UN-conjugates: a crossing before the above-padded gadget converts to
the below-padded gadget sandwiched by the two crossing orientations. -/
theorem lcxUpperGadgetUnconjugates (scaleFactor : Nat) :
    SldAreConvertibleLayers 3
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: []))
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList scaleFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.crossing, SldCell.wire] :: [])) := by
  have conjugationBack := SldAreConvertibleLayers.fromSymmetry
    (lcxGadgetRidesConjugationShaped scaleFactor)
  have appended := sldConvAppendsSuffix conjugationBack [[SldCell.crossing, SldCell.wire]]
  simp only [lcxAppendLayersConsExposes, lcxAppendLayersNilExposes, sldAppendLayersAssoc]
    at appended
  have trailingPairDies : SldAreConvertibleLayers 3
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire] :: []))
      ([SldCell.crossing, SldCell.wire]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList scaleFactor))
            ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing] :: [])) := by
    refine sldConvUnderPrefixList
      [[SldCell.crossing, SldCell.wire],
        [SldCell.wire, SldCell.wire, SldCell.generatorDelta]] 3 _ _ ?_
    refine sldConvUnderPrefixList (sldPadWindow 2 1 (lstScaleLayerList scaleFactor)) 4 _ _ ?_
    rw [lcxWindowTwoOneReachFromFour]
    exact sldConvUnderPrefixList
      [[SldCell.wire, SldCell.generatorMu, SldCell.wire],
        [SldCell.wire, SldCell.crossing]] 4 _ _
      (lcoTauPairDiesOverWire [])
  exact SldAreConvertibleLayers.fromTransitivity
    (SldAreConvertibleLayers.fromSymmetry trailingPairDies) appended

/-- THE TWO-GADGET SWAP ACROSS THE CROSSING: swapping the two sources and merging in order
`first, second` converts to merging in order `second, first` followed by the accumulator
crossing.  Assembled from the un-conjugation of the upper gadget, Yang-Baxter, the
far-pregadget commutation, an S1 pair kill, and the shaped conjugation. -/
theorem lcxGadgetPairSwapsAcrossCrossing (firstFactor secondFactor : Nat) :
    SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: sldAppendLayers (sldPadLayersBelow 1 (lstGadgetLayerList firstFactor))
            (sldPadLayersAbove 1 (lstGadgetLayerList secondFactor)))
      (sldAppendLayers (sldPadLayersBelow 1 (lstGadgetLayerList secondFactor))
        (sldAppendLayers (sldPadLayersAbove 1 (lstGadgetLayerList firstFactor))
          [[SldCell.crossing, SldCell.wire]])) := by
  rw [lcxGadgetPadBelowShape firstFactor, lcxGadgetPadAboveShape secondFactor,
    lcxGadgetPadBelowShape secondFactor, lcxGadgetPadAboveShape firstFactor]
  simp only [lcxAppendLayersConsExposes, lcxAppendLayersNilExposes, sldAppendLayersAssoc]
  -- Step 1: the upper gadget un-conjugates behind the first column.
  have upperUnconjugates : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList secondFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.crossing, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.crossing, SldCell.wire] :: []))) := by
    refine SldAreConvertibleLayers.underLayerPrefix 3 [SldCell.wire, SldCell.crossing] ?_
    refine SldAreConvertibleLayers.underLayerPrefix 3
      [SldCell.wire, SldCell.generatorDelta, SldCell.wire] ?_
    refine sldConvUnderPrefixList (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) 4 _ _ ?_
    rw [lcxWindowOneTwoReachFromFour]
    exact SldAreConvertibleLayers.underLayerPrefix 4
      [SldCell.generatorMu, SldCell.wire, SldCell.wire]
      (lcxUpperGadgetUnconjugates secondFactor)
  -- Step 2: Yang-Baxter realigns the second column's crossing tail.
  have braidRealigns : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.crossing, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.crossing, SldCell.wire] :: [])))
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.crossing, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: []))) := by
    refine SldAreConvertibleLayers.underLayerPrefix 3 [SldCell.wire, SldCell.crossing] ?_
    refine SldAreConvertibleLayers.underLayerPrefix 3
      [SldCell.wire, SldCell.generatorDelta, SldCell.wire] ?_
    refine sldConvUnderPrefixList (sldPadWindow 1 2 (lstScaleLayerList firstFactor)) 4 _ _ ?_
    rw [lcxWindowOneTwoReachFromFour]
    refine SldAreConvertibleLayers.underLayerPrefix 4
      [SldCell.generatorMu, SldCell.wire, SldCell.wire] ?_
    refine SldAreConvertibleLayers.underLayerPrefix 3 [SldCell.wire, SldCell.crossing] ?_
    refine SldAreConvertibleLayers.underLayerPrefix 3
      [SldCell.wire, SldCell.generatorDelta, SldCell.wire] ?_
    refine sldConvUnderPrefixList (sldPadWindow 1 2 (lstScaleLayerList secondFactor)) 4 _ _ ?_
    rw [lcxWindowOneTwoReachFromFour]
    exact SldAreConvertibleLayers.underLayerPrefix 4
      [SldCell.generatorMu, SldCell.wire, SldCell.wire]
      (SldAreConvertibleLayers.fromSwapYangBaxterRow 0 0 [])
  -- Step 3: the far pregadgets commute (with the crossing-pair suffix).
  have farCommutes : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.crossing, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.crossing, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: []))) := by
    have farWithSuffix := sldConvAppendsSuffix
      (lcxFarPregadgetsCommute firstFactor secondFactor)
      ([SldCell.crossing, SldCell.wire] :: [SldCell.wire, SldCell.crossing] :: [])
    simp only [lcxAppendLayersConsExposes, lcxAppendLayersNilExposes, sldAppendLayersAssoc]
      at farWithSuffix
    exact SldAreConvertibleLayers.underLayerPrefix 3 [SldCell.wire, SldCell.crossing]
      farWithSuffix
  -- Step 4: the leading crossing pair dies.
  have leadingPairDies : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.crossing]
        :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.crossing, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.crossing, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: []))) :=
    lcoTauPairDiesUnderWire
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.crossing, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: [])))
  -- Step 5: the first column re-conjugates behind the second column.
  have firstReconjugates : SldAreConvertibleLayers 3
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.wire, SldCell.crossing]
              :: [SldCell.wire, SldCell.generatorDelta, SldCell.wire]
              :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList firstFactor))
                  ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
                    :: [SldCell.crossing, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing] :: [])))
      ([SldCell.wire, SldCell.generatorDelta, SldCell.wire]
        :: sldAppendLayers (sldPadWindow 1 2 (lstScaleLayerList secondFactor))
            ([SldCell.generatorMu, SldCell.wire, SldCell.wire]
              :: [SldCell.crossing, SldCell.wire]
              :: [SldCell.wire, SldCell.wire, SldCell.generatorDelta]
              :: sldAppendLayers (sldPadWindow 2 1 (lstScaleLayerList firstFactor))
                  ([SldCell.wire, SldCell.generatorMu, SldCell.wire]
                    :: [SldCell.wire, SldCell.crossing]
                    :: [SldCell.crossing, SldCell.wire] :: []))) := by
    refine SldAreConvertibleLayers.underLayerPrefix 3
      [SldCell.wire, SldCell.generatorDelta, SldCell.wire] ?_
    refine sldConvUnderPrefixList (sldPadWindow 1 2 (lstScaleLayerList secondFactor)) 4 _ _ ?_
    rw [lcxWindowOneTwoReachFromFour]
    exact SldAreConvertibleLayers.underLayerPrefix 4
      [SldCell.generatorMu, SldCell.wire, SldCell.wire]
      (lcxGadgetRidesConjugationShaped firstFactor)
  exact SldAreConvertibleLayers.fromTransitivity upperUnconjugates
    (SldAreConvertibleLayers.fromTransitivity braidRealigns
      (SldAreConvertibleLayers.fromTransitivity farCommutes
        (SldAreConvertibleLayers.fromTransitivity leadingPairDies firstReconjugates)))

/-! ## Chunk 6: THE CROSSING BOTTOM CORE — the fan-level source-climb induction -/

/-- THE CROSSING BOTTOM CORE: two adjacent column fans swap when their sources swap —
`(wires(t) | tau) ; (fan(t, A) | wire) ; fan(t, B) ~ (fan(t, B) | wire) ; fan(t, A)`.
Source-climb induction in the mu/delta-core template: the base is the Neps row plus one
disjoint exchange; each rung converts the freshly-peeled gadget pair by the PADDED
TWO-GADGET SWAP, feeds the emitted below-crossing to the BELOW-PADDED INDUCTION HYPOTHESIS,
and realigns the fan blocks by the Godement block slides. -/
theorem lcxCrossingTwoFanSwap : (vectorLength : Nat) -> (firstColumn secondColumn : Nat -> Nat) ->
    SldAreConvertibleLayers (vectorLength + 2)
      (sldAppendCells (sldWireLayerOfArity vectorLength) [SldCell.crossing]
        :: sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList vectorLength firstColumn))
            (lstFanLayerList vectorLength secondColumn))
      (sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList vectorLength secondColumn))
        (lstFanLayerList vectorLength firstColumn))
  | 0, firstColumn, secondColumn => by
      rw [lstFanZeroLayerShape firstColumn, lstFanZeroLayerShape secondColumn]
      have discardCrossesSwap : SldAreConvertibleLayers 2
          ([SldCell.crossing]
            :: [SldCell.generatorEpsilon, SldCell.wire]
            :: [SldCell.generatorEpsilon] :: [])
          ([SldCell.wire, SldCell.generatorEpsilon] :: [SldCell.generatorEpsilon] :: []) :=
        SldAreConvertibleLayers.fromDiscardPastSwapRow 0 0 [[SldCell.generatorEpsilon]]
      have discardsExchange : SldAreConvertibleLayers 2
          ([SldCell.generatorEpsilon, SldCell.wire] :: [SldCell.generatorEpsilon] :: [])
          ([SldCell.wire, SldCell.generatorEpsilon] :: [SldCell.generatorEpsilon] :: []) :=
        sldDisjointLayersExchange [SldCell.generatorEpsilon] [SldCell.generatorEpsilon] []
      exact SldAreConvertibleLayers.fromTransitivity discardCrossesSwap
        (SldAreConvertibleLayers.fromSymmetry discardsExchange)
  | vectorLengthPred + 1, firstColumn, secondColumn => by
      rw [lstFanSuccUnfolds vectorLengthPred firstColumn,
        lstFanSuccUnfolds vectorLengthPred secondColumn]
      have leftPadShape : sldPadLayersBelow 1
          (sldAppendLayers
            (sldPadLayersAbove vectorLengthPred
              (lstGadgetLayerList (firstColumn vectorLengthPred)))
            (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred firstColumn)))
          = sldAppendLayers
              (sldPadWindow vectorLengthPred 1
                (lstGadgetLayerList (firstColumn vectorLengthPred)))
              (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn)) := by
        rw [sldPadLayersBelowOfAppend, lstPadBelowOfPadAboveIsPadWindow,
          lstPadLayersBelowCompose]
      have rightPadShape : sldPadLayersBelow 1
          (sldAppendLayers
            (sldPadLayersAbove vectorLengthPred
              (lstGadgetLayerList (secondColumn vectorLengthPred)))
            (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred secondColumn)))
          = sldAppendLayers
              (sldPadWindow vectorLengthPred 1
                (lstGadgetLayerList (secondColumn vectorLengthPred)))
              (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred secondColumn)) := by
        rw [sldPadLayersBelowOfAppend, lstPadBelowOfPadAboveIsPadWindow,
          lstPadLayersBelowCompose]
      rw [leftPadShape, rightPadShape]
      simp only [sldAppendLayersAssoc]
      -- Reach bookkeeping.
      have headWalk : sldLayerTargetArity
          (sldAppendCells (sldWireLayerOfArity (vectorLengthPred + 1)) [SldCell.crossing])
          = vectorLengthPred + 1 + 2 := by
        rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
        rfl
      have windowWalkFirst : sldLayersTargetArityFrom (vectorLengthPred + 1 + 2)
          (sldPadWindow vectorLengthPred 1 (lstGadgetLayerList (firstColumn vectorLengthPred)))
          = vectorLengthPred + 3 := by
        have liftedReach := sldPadWindowTargetArityFrom vectorLengthPred 1
          (lstGadgetLayerList (firstColumn vectorLengthPred)) 2
        rw [lstGadgetLayersReach] at liftedReach
        exact liftedReach
      have windowWalkSecond : sldLayersTargetArityFrom (vectorLengthPred + 1 + 2)
          (sldPadWindow vectorLengthPred 1 (lstGadgetLayerList (secondColumn vectorLengthPred)))
          = vectorLengthPred + 3 := by
        have liftedReach := sldPadWindowTargetArityFrom vectorLengthPred 1
          (lstGadgetLayerList (secondColumn vectorLengthPred)) 2
        rw [lstGadgetLayersReach] at liftedReach
        exact liftedReach
      have aboveWalkFirst : sldLayersTargetArityFrom (vectorLengthPred + 3)
          (sldPadLayersAbove (vectorLengthPred + 1)
            (lstGadgetLayerList (firstColumn vectorLengthPred)))
          = vectorLengthPred + 3 := by
        have liftedReach := sldPadLayersAboveTargetArityFrom (vectorLengthPred + 1)
          (lstGadgetLayerList (firstColumn vectorLengthPred)) 2
        rw [lstGadgetLayersReach] at liftedReach
        exact liftedReach
      -- Phase A: the second gadget climbs above the first fan block.
      have gadgetClimbsAboveFan : SldAreConvertibleLayers (vectorLengthPred + 1 + 2)
          (sldAppendCells (sldWireLayerOfArity (vectorLengthPred + 1)) [SldCell.crossing]
            :: sldAppendLayers
                (sldPadWindow vectorLengthPred 1
                  (lstGadgetLayerList (firstColumn vectorLengthPred)))
                (sldAppendLayers
                  (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
                  (sldAppendLayers
                    (sldPadLayersAbove vectorLengthPred
                      (lstGadgetLayerList (secondColumn vectorLengthPred)))
                    (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred secondColumn)))))
          (sldAppendCells (sldWireLayerOfArity (vectorLengthPred + 1)) [SldCell.crossing]
            :: sldAppendLayers
                (sldPadWindow vectorLengthPred 1
                  (lstGadgetLayerList (firstColumn vectorLengthPred)))
                (sldAppendLayers
                  (sldPadLayersAbove (vectorLengthPred + 1)
                    (lstGadgetLayerList (secondColumn vectorLengthPred)))
                  (sldAppendLayers
                    (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
                    (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred secondColumn))))) := by
        refine SldAreConvertibleLayers.underLayerPrefix (vectorLengthPred + 1 + 2)
          (sldAppendCells (sldWireLayerOfArity (vectorLengthPred + 1)) [SldCell.crossing]) ?_
        rw [headWalk]
        refine sldConvUnderPrefixList
          (sldPadWindow vectorLengthPred 1
            (lstGadgetLayerList (firstColumn vectorLengthPred)))
          (vectorLengthPred + 1 + 2) _ _ ?_
        rw [windowWalkFirst]
        have slideInstance := sldBlockSlidesDownPastBlock
          (lstFanLayerList vectorLengthPred firstColumn) (vectorLengthPred + 1)
          (lstFanLayersAreComposable vectorLengthPred firstColumn)
          (lstGadgetLayerList (secondColumn vectorLengthPred)) 2
          (lstGadgetLayersAreComposable (secondColumn vectorLengthPred))
          (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred secondColumn))
        rw [lstFanLayersReach, lstGadgetLayersReach] at slideInstance
        exact slideInstance
      -- Phase B: the padded two-gadget swap fires at the fresh strands.
      have pairSwapsAtWindow : SldAreConvertibleLayers (vectorLengthPred + 1 + 2)
          (sldAppendCells (sldWireLayerOfArity (vectorLengthPred + 1)) [SldCell.crossing]
            :: sldAppendLayers
                (sldPadWindow vectorLengthPred 1
                  (lstGadgetLayerList (firstColumn vectorLengthPred)))
                (sldAppendLayers
                  (sldPadLayersAbove (vectorLengthPred + 1)
                    (lstGadgetLayerList (secondColumn vectorLengthPred)))
                  (sldAppendLayers
                    (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
                    (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred secondColumn)))))
          (sldAppendLayers
            (sldPadWindow vectorLengthPred 1
              (lstGadgetLayerList (secondColumn vectorLengthPred)))
            (sldAppendLayers
              (sldPadLayersAbove (vectorLengthPred + 1)
                (lstGadgetLayerList (firstColumn vectorLengthPred)))
              (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                  [SldCell.crossing, SldCell.wire]
                :: sldAppendLayers
                    (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
                    (sldPadLayersBelow 1
                      (lstFanLayerList vectorLengthPred secondColumn))))) := by
        have paddedSwap := lcoConvPadsWindow
          (lcxGadgetPairSwapsAcrossCrossing (firstColumn vectorLengthPred)
            (secondColumn vectorLengthPred)) vectorLengthPred 0
        rw [show sldPadWindow vectorLengthPred 0
              ([SldCell.wire, SldCell.crossing]
                :: sldAppendLayers
                    (sldPadLayersBelow 1
                      (lstGadgetLayerList (firstColumn vectorLengthPred)))
                    (sldPadLayersAbove 1
                      (lstGadgetLayerList (secondColumn vectorLengthPred))))
            = sldPadLayer vectorLengthPred 0 [SldCell.wire, SldCell.crossing]
              :: sldPadWindow vectorLengthPred 0
                  (sldAppendLayers
                    (sldPadLayersBelow 1
                      (lstGadgetLayerList (firstColumn vectorLengthPred)))
                    (sldPadLayersAbove 1
                      (lstGadgetLayerList (secondColumn vectorLengthPred)))) from rfl,
          lcoPadWindowOfAppendLayers vectorLengthPred 0
            (sldPadLayersBelow 1 (lstGadgetLayerList (firstColumn vectorLengthPred)))
            (sldPadLayersAbove 1 (lstGadgetLayerList (secondColumn vectorLengthPred))),
          lcoPadWindowOfPadLayersBelow vectorLengthPred 0 1
            (lstGadgetLayerList (firstColumn vectorLengthPred)),
          lcoPadWindowOfPadLayersAbove vectorLengthPred 1 0
            (lstGadgetLayerList (secondColumn vectorLengthPred)),
          lcxPadWindowWithZeroBelowIsPadAbove (vectorLengthPred + 1)
            (lstGadgetLayerList (secondColumn vectorLengthPred)),
          lcoPadWindowOfAppendLayers vectorLengthPred 0
            (sldPadLayersBelow 1 (lstGadgetLayerList (secondColumn vectorLengthPred)))
            (sldAppendLayers
              (sldPadLayersAbove 1 (lstGadgetLayerList (firstColumn vectorLengthPred)))
              [[SldCell.crossing, SldCell.wire]]),
          lcoPadWindowOfPadLayersBelow vectorLengthPred 0 1
            (lstGadgetLayerList (secondColumn vectorLengthPred)),
          lcoPadWindowOfAppendLayers vectorLengthPred 0
            (sldPadLayersAbove 1 (lstGadgetLayerList (firstColumn vectorLengthPred)))
            [[SldCell.crossing, SldCell.wire]],
          lcoPadWindowOfPadLayersAbove vectorLengthPred 1 0
            (lstGadgetLayerList (firstColumn vectorLengthPred)),
          lcxPadWindowWithZeroBelowIsPadAbove (vectorLengthPred + 1)
            (lstGadgetLayerList (firstColumn vectorLengthPred)),
          show sldPadLayer vectorLengthPred 0 [SldCell.wire, SldCell.crossing]
            = sldAppendCells (sldWireLayerOfArity (vectorLengthPred + 1)) [SldCell.crossing]
            from by
              show sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                  (sldAppendCells [SldCell.wire, SldCell.crossing] (sldWireLayerOfArity 0))
                = sldAppendCells (sldWireLayerOfArity (vectorLengthPred + 1))
                    [SldCell.crossing]
              rw [(sldWireLayerSplitsAtCount vectorLengthPred 1).symm, sldAppendCellsAssoc]
              rfl] at paddedSwap
        have swapWithSuffix := sldConvAppendsSuffix paddedSwap
          (sldAppendLayers
            (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
            (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred secondColumn)))
        simp only [lcxAppendLayersConsExposes, sldAppendLayersAssoc] at swapWithSuffix
        exact swapWithSuffix
      -- Phase C: the emitted crossing plus the two fans ARE the below-padded shorter swap.
      have innerSwapRecurses : SldAreConvertibleLayers (vectorLengthPred + 1 + 2)
          (sldAppendLayers
            (sldPadWindow vectorLengthPred 1
              (lstGadgetLayerList (secondColumn vectorLengthPred)))
            (sldAppendLayers
              (sldPadLayersAbove (vectorLengthPred + 1)
                (lstGadgetLayerList (firstColumn vectorLengthPred)))
              (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                  [SldCell.crossing, SldCell.wire]
                :: sldAppendLayers
                    (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred firstColumn))
                    (sldPadLayersBelow 1
                      (lstFanLayerList vectorLengthPred secondColumn)))))
          (sldAppendLayers
            (sldPadWindow vectorLengthPred 1
              (lstGadgetLayerList (secondColumn vectorLengthPred)))
            (sldAppendLayers
              (sldPadLayersAbove (vectorLengthPred + 1)
                (lstGadgetLayerList (firstColumn vectorLengthPred)))
              (sldAppendLayers
                (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred secondColumn))
                (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred firstColumn))))) := by
        refine sldConvUnderPrefixList
          (sldPadWindow vectorLengthPred 1
            (lstGadgetLayerList (secondColumn vectorLengthPred)))
          (vectorLengthPred + 1 + 2) _ _ ?_
        rw [windowWalkSecond]
        refine sldConvUnderPrefixList
          (sldPadLayersAbove (vectorLengthPred + 1)
            (lstGadgetLayerList (firstColumn vectorLengthPred)))
          (vectorLengthPred + 3) _ _ ?_
        rw [aboveWalkFirst]
        have paddedRecursion := sldConvPadsBelow
          (lcxCrossingTwoFanSwap vectorLengthPred firstColumn secondColumn) 1
        rw [show sldPadLayersBelow 1
              (sldAppendCells (sldWireLayerOfArity vectorLengthPred) [SldCell.crossing]
                :: sldAppendLayers
                    (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred firstColumn))
                    (lstFanLayerList vectorLengthPred secondColumn))
            = sldAppendCells
                (sldAppendCells (sldWireLayerOfArity vectorLengthPred) [SldCell.crossing])
                (sldWireLayerOfArity 1)
              :: sldPadLayersBelow 1
                  (sldAppendLayers
                    (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred firstColumn))
                    (lstFanLayerList vectorLengthPred secondColumn)) from rfl,
          sldPadLayersBelowOfAppend 1
            (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred firstColumn))
            (lstFanLayerList vectorLengthPred secondColumn),
          lstPadLayersBelowCompose 1 1 (lstFanLayerList vectorLengthPred firstColumn),
          sldPadLayersBelowOfAppend 1
            (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred secondColumn))
            (lstFanLayerList vectorLengthPred firstColumn),
          lstPadLayersBelowCompose 1 1 (lstFanLayerList vectorLengthPred secondColumn),
          sldAppendCellsAssoc (sldWireLayerOfArity vectorLengthPred) [SldCell.crossing]
            (sldWireLayerOfArity 1)] at paddedRecursion
        exact paddedRecursion
      -- Phase D: the fan blocks realign (Godement block slide back).
      have fanBlocksRealign : SldAreConvertibleLayers (vectorLengthPred + 1 + 2)
          (sldAppendLayers
            (sldPadWindow vectorLengthPred 1
              (lstGadgetLayerList (secondColumn vectorLengthPred)))
            (sldAppendLayers
              (sldPadLayersAbove (vectorLengthPred + 1)
                (lstGadgetLayerList (firstColumn vectorLengthPred)))
              (sldAppendLayers
                (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred secondColumn))
                (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred firstColumn)))))
          (sldAppendLayers
            (sldPadWindow vectorLengthPred 1
              (lstGadgetLayerList (secondColumn vectorLengthPred)))
            (sldAppendLayers
              (sldPadLayersBelow 2 (lstFanLayerList vectorLengthPred secondColumn))
              (sldAppendLayers
                (sldPadLayersAbove vectorLengthPred
                  (lstGadgetLayerList (firstColumn vectorLengthPred)))
                (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred firstColumn))))) := by
        refine sldConvUnderPrefixList
          (sldPadWindow vectorLengthPred 1
            (lstGadgetLayerList (secondColumn vectorLengthPred)))
          (vectorLengthPred + 1 + 2) _ _ ?_
        rw [windowWalkSecond]
        have slideInstance := sldBlockSlidesDownPastBlock
          (lstFanLayerList vectorLengthPred secondColumn) (vectorLengthPred + 1)
          (lstFanLayersAreComposable vectorLengthPred secondColumn)
          (lstGadgetLayerList (firstColumn vectorLengthPred)) 2
          (lstGadgetLayersAreComposable (firstColumn vectorLengthPred))
          (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred firstColumn))
        rw [lstFanLayersReach, lstGadgetLayersReach] at slideInstance
        exact SldAreConvertibleLayers.fromSymmetry slideInstance
      exact SldAreConvertibleLayers.fromTransitivity gadgetClimbsAboveFan
        (SldAreConvertibleLayers.fromTransitivity pairSwapsAtWindow
          (SldAreConvertibleLayers.fromTransitivity innerSwapRecurses fanBlocksRealign))

/-! ## The flip, the fires, and the honest ledger -/

/-- THE CROSSING TWO-FAN-SWAP STATEMENT IS INHABITED (ascription against the live Prop
verbatim).  Attack 2 — the conjugation route — closed the core the braid-alignment attack
burned on. -/
theorem lcxCrossingTwoFanSwapHolds : lstCrossingTwoFanSwapStatement :=
  fun vectorLength firstColumn secondColumn =>
    lcxCrossingTwoFanSwap vectorLength firstColumn secondColumn

/-- CROSSING-CORE FIRE (t = 1, columns 1 and 2): the two-fan swap at the smallest genuine
fan pair. -/
theorem lcxCrossingCoreFire :
    SldAreConvertibleLayers 3
      (sldAppendCells (sldWireLayerOfArity 1) [SldCell.crossing]
        :: sldAppendLayers
            (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 1)))
            (lstFanLayerList 1 (fun _sourceRow => 2)))
      (sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 2)))
        (lstFanLayerList 1 (fun _sourceRow => 1))) :=
  lcxCrossingTwoFanSwap 1 (fun _sourceRow => 1) (fun _sourceRow => 2)

/-- CROSSING-CORE FIRE consumed through soundness: both sides denote the same matrix on the
1x3 rectangle — `acc + 1 * y + 2 * x = acc + 2 * x + 1 * y`. -/
theorem lcxCrossingCoreFireDenotesEqually :
    doEntriesAgreeUpTo 1 3
      (sldLayersDenote
        (sldAppendCells (sldWireLayerOfArity 1) [SldCell.crossing]
          :: sldAppendLayers
              (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 1)))
              (lstFanLayerList 1 (fun _sourceRow => 2))))
      (sldLayersDenote
        (sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList 1 (fun _sourceRow => 2)))
          (lstFanLayerList 1 (fun _sourceRow => 1)))) = true :=
  sldConvertibleLayersDenoteAgreeUpTo lcxCrossingCoreFire 1

/-- CONJUGATION FIRE consumed through soundness: the conjugated gadget windows denote the
same matrix on the 3x3 rectangle (scale two). -/
theorem lcxConjugationFireDenotesEqually :
    doEntriesAgreeUpTo 3 3
      (sldLayersDenote
        ([SldCell.wire, SldCell.crossing]
          :: sldAppendLayers (sldPadLayersBelow 1 (lstGadgetLayerList 2))
              [[SldCell.wire, SldCell.crossing]]))
      (sldLayersDenote
        ([SldCell.crossing, SldCell.wire]
          :: sldAppendLayers (sldPadLayersAbove 1 (lstGadgetLayerList 2))
              [[SldCell.crossing, SldCell.wire]])) = true :=
  sldConvertibleLayersDenoteAgreeUpTo (lcxGadgetRidesConjugation 2) 3

/-- TWO-GADGET-SWAP FIRE consumed through soundness (scales 1 and 2, 3x3 rectangle). -/
theorem lcxGadgetPairSwapFireDenotesEqually :
    doEntriesAgreeUpTo 3 3
      (sldLayersDenote
        ([SldCell.wire, SldCell.crossing]
          :: sldAppendLayers (sldPadLayersBelow 1 (lstGadgetLayerList 1))
              (sldPadLayersAbove 1 (lstGadgetLayerList 2))))
      (sldLayersDenote
        (sldAppendLayers (sldPadLayersBelow 1 (lstGadgetLayerList 2))
          (sldAppendLayers (sldPadLayersAbove 1 (lstGadgetLayerList 1))
            [[SldCell.crossing, SldCell.wire]]))) = true :=
  sldConvertibleLayersDenoteAgreeUpTo (lcxGadgetPairSwapsAcrossCrossing 1 2) 3

/-- NEGATIVE CONTROL re-confirmed over the crossing core: fans of DISTINCT columns stay
non-convertible — the new conversion machinery did not collapse the semantics. -/
theorem lcxDistinctColumnFansStayApart :
    SldAreConvertibleLayers 2 (lstFanLayerList 1 (fun _sourceRow => 1))
      (lstFanLayerList 1 (fun _sourceRow => 2)) -> False :=
  sldNotConvertibleOfDistinctDenotes (lstFanLayerList 1 (fun _sourceRow => 1))
    (lstFanLayerList 1 (fun _sourceRow => 2)) 1 rfl

/-- Marker (true): the crossing bottom core of the Lafont staircase is CLOSED — the
two-fan-swap statement is inhabited via the conjugation route (attack 2): the one-gadget
conjugation, the far-pregadget commutation through the canonical parallel form, the
two-gadget swap, and the fan-level source-climb induction.  All three bottom cores
(mu, delta, crossing) of the absorption ladder now hold; the frozen owner Bools
`lstCrossingTwoFanSwapProved` / `lcoCrossingTwoFanSwapProved` stay byte-intact false as
history, superseded by `lcxCrossingTwoFanSwapHolds`. -/
def fxLafontStaircase_hasCrossingCore : Bool := true
