import FX1Poly.Polygraph.Omega.LafontProp.StaircaseCrossingCore

/-! # Polygraph/Omega/LafontProp/StaircaseAssembly — THE ASSEMBLY: canonical reduction over
strict layers (LAFONT-REPAIR stage 2 phase 5: the completeness statement lands)

All six cell bottom cores are DECIDED upstream (wire/eta/epsilon in `StaircaseCompleteness`,
mu/delta in `StaircaseCores`, crossing in `StaircaseCrossingCore`).  This file consumes them
and assembles the frozen owner Prop `lstCanonicalReductionOverStrictLayersStatement`:

* (i)   mu/delta/crossing BOTTOM-CORE-TO-ABSORPTION ALIGNMENT — matrix-patch lemmas for the
        padded mu/delta/tau fresh columns, then per-cell absorption at pad zero: one
        canonical unfold, one `sldLowerLayerSlidesDownPastBlock` past the shorter canonical
        block, the decided core, refold via rectangle/column agreement.
* (ii)  the generic below-pad lift instances (`lstCellAbsorptionLiftsThroughBelowPads`) for
        mu/delta/crossing, and the SIX-WAY single-cell dispatcher.
* (iii) MULTI-CELL LAYER DECOMPOSITION — a whole layer absorbs into the canonical form by
        cell recursion through `layerSplitTopActsFirst`, with the split-product agreement
        discharged through the congruence's own Mat(N) soundness.
* (iv)  the LAYER-LIST INDUCTION over the diagram.
* (v)   THE IDENTITY-FORM DISSOLUTION — `canonical(n, n, identity)` converts to the EMPTY
        layer list: the one genuinely new induction (unit-column fan analysis): the fresh
        source climbs the eta stack by gadget-zero crossings and Neta, and dies into the
        diagonal gadget-one whose fresh-zero input makes it a copy that the counit kills.
* (vi)  `lsaCanonicalReductionHolds : lstCanonicalReductionOverStrictLayersStatement` by
        direct ascription, THE DECISION BICONDITIONAL over `SldDiagram`, fires, a kernel-rfl
        negative control, and the content marker
        `fxLafontStaircase_canonicalCompletenessProven := true`.

The frozen owners `lstCanonicalReductionOverStrictLayersProved` (StaircaseCompleteness) and
`fxLafontStrictLayer_hasCanonicalCompleteness` (StrictLayerEmbedding) stay byte-intact false
in their committed files, superseded by this file's content marker.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; audit twin with per-decl
`#assert_no_axioms` plus an independent `#print axioms` probe. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.LafontProp

/-! ## Small order/ne helpers (hand-rolled, leak-free) -/

/-- A strictly smaller Nat is different. -/
theorem lsaNeOfLt {smallNat bigNat : Nat} (isBelow : smallNat < bigNat) :
    smallNat ≠ bigNat :=
  fun areEqual => noLtOfEq areEqual isBelow

/-- A strictly bigger Nat is different (the flipped orientation). -/
theorem lsaNeOfGt {smallNat bigNat : Nat} (isBelow : smallNat < bigNat) :
    bigNat ≠ smallNat :=
  fun areEqual => noLtOfEq areEqual.symm isBelow

/-- Any Nat is strictly below itself plus a successor. -/
theorem lsaLtAddSucc (baseNat offsetPred : Nat) : baseNat < baseNat + (offsetPred + 1) :=
  sldAddLeAddLeft baseNat (Nat.succ_le_succ (Nat.zero_le offsetPred))

/-! ## The deep-cell layer entry kit: what `wires(p) | cell` reads blockwise -/

/-- A deep-cell layer entry in the wire rows at a fresh column is 0 (top-right block). -/
theorem lsaDeepCellLayerEntryInWireRows (deepCell : SldCell) (padAboveCount : Nat)
    {rowIndex : Nat} (colOffset : Nat) (isRowInPad : rowIndex < padAboveCount) :
    sldLayerEntries (sldAppendCells (sldWireLayerOfArity padAboveCount) [deepCell])
        rowIndex (padAboveCount + colOffset)
      = 0 := by
  have blockForm := sldAppendCellsEntriesAsBlocks (sldWireLayerOfArity padAboveCount)
    [deepCell] rowIndex (padAboveCount + colOffset)
  rw [sldWireLayerTargetArity, sldWireLayerSourceArity,
    directSumEntryInTopRightBlock _ _ colOffset isRowInPad] at blockForm
  exact blockForm

/-- A deep-cell layer entry at pad offsets reads the bare cell's own layer entries
(bottom-right block). -/
theorem lsaDeepCellLayerEntryAtPadOffset (deepCell : SldCell) (padAboveCount : Nat)
    (rowOffset colOffset : Nat) :
    sldLayerEntries (sldAppendCells (sldWireLayerOfArity padAboveCount) [deepCell])
        (padAboveCount + rowOffset) (padAboveCount + colOffset)
      = sldLayerEntries [deepCell] rowOffset colOffset := by
  have blockForm := sldAppendCellsEntriesAsBlocks (sldWireLayerOfArity padAboveCount)
    [deepCell] (padAboveCount + rowOffset) (padAboveCount + colOffset)
  rw [sldWireLayerTargetArity, sldWireLayerSourceArity,
    directSumEntryInBottomBlock _ _ rowOffset colOffset] at blockForm
  exact blockForm

/-- The wire-row head of a product against a deep-cell layer at a fresh column vanishes. -/
theorem lsaDeepCellHeadSumVanishes (deepCell : SldCell) (padAboveCount : Nat)
    (entries : MatrixEntries) (rowIndex colOffset : Nat) :
    sumBelow (fun middleIndex => entries rowIndex middleIndex
        * sldLayerEntries (sldAppendCells (sldWireLayerOfArity padAboveCount) [deepCell])
            middleIndex (padAboveCount + colOffset)) padAboveCount
      = 0 :=
  sumBelowOfAllZeroIsZero _ padAboveCount (fun middleIndex isMiddleInPad => by
    show entries rowIndex middleIndex
        * sldLayerEntries (sldAppendCells (sldWireLayerOfArity padAboveCount) [deepCell])
            middleIndex (padAboveCount + colOffset)
      = 0
    rw [lsaDeepCellLayerEntryInWireRows deepCell padAboveCount colOffset isMiddleInPad]
    rfl)

/-- Multiplying by any deep-cell layer `wires(p) | cell` reads the plain matrix at columns
inside the wire prefix — generic across all six cell kinds. -/
theorem lsaProductThroughDeepCellReadsPrefix (deepCell : SldCell) (padAboveCount : Nat)
    (entries : MatrixEntries) (rowIndex colIndex : Nat)
    (isColInside : colIndex < padAboveCount) :
    composeEntries (padAboveCount + sldCellTargetArity deepCell) entries
        (sldLayerEntries (sldAppendCells (sldWireLayerOfArity padAboveCount) [deepCell]))
        rowIndex colIndex
      = entries rowIndex colIndex := by
  have isColInsideWireSource :
      colIndex < sldLayerSourceArity (sldWireLayerOfArity padAboveCount) := by
    rw [sldWireLayerSourceArity]
    exact isColInside
  have restricted := lstProductAgainstAppendedLayerRestricts
    (sldWireLayerOfArity padAboveCount) [deepCell] entries rowIndex colIndex
    isColInsideWireSource
  rw [sldWireLayerTargetArity] at restricted
  exact restricted.trans
    (lstProductThroughWireLayerCollapses padAboveCount entries rowIndex colIndex isColInside)

/-! ## The fresh-column matrix patches for the padded mu / delta / tau layers -/

/-- MU PATCH, low fresh column: `(M * (wires(p) | mu))(r, p) = M(r, p)`. -/
theorem lsaDeepMuProductFreshLowColumn (padAboveCount : Nat) (entries : MatrixEntries)
    (rowIndex : Nat) :
    composeEntries (padAboveCount + 1) entries
        (sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorMu]))
        rowIndex padAboveCount
      = entries rowIndex padAboveCount := by
  show sumBelow (fun middleIndex => entries rowIndex middleIndex
        * sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorMu])
            middleIndex (padAboveCount + 0)) padAboveCount
      + entries rowIndex padAboveCount
        * sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorMu])
            (padAboveCount + 0) (padAboveCount + 0)
    = entries rowIndex padAboveCount
  rw [lsaDeepCellHeadSumVanishes SldCell.generatorMu padAboveCount entries rowIndex 0,
    lsaDeepCellLayerEntryAtPadOffset SldCell.generatorMu padAboveCount 0 0]
  show 0 + entries rowIndex padAboveCount * 1 = entries rowIndex padAboveCount
  rw [mulOneIsSelf (entries rowIndex padAboveCount)]
  exact Nat.zero_add (entries rowIndex padAboveCount)

/-- MU PATCH, high fresh column: `(M * (wires(p) | mu))(r, p + 1) = M(r, p)` — both fresh
columns of the padded add read the SAME source column, the duplication the fan mirrors. -/
theorem lsaDeepMuProductFreshHighColumn (padAboveCount : Nat) (entries : MatrixEntries)
    (rowIndex : Nat) :
    composeEntries (padAboveCount + 1) entries
        (sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorMu]))
        rowIndex (padAboveCount + 1)
      = entries rowIndex padAboveCount := by
  show sumBelow (fun middleIndex => entries rowIndex middleIndex
        * sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorMu])
            middleIndex (padAboveCount + 1)) padAboveCount
      + entries rowIndex padAboveCount
        * sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorMu])
            (padAboveCount + 0) (padAboveCount + 1)
    = entries rowIndex padAboveCount
  rw [lsaDeepCellHeadSumVanishes SldCell.generatorMu padAboveCount entries rowIndex 1,
    lsaDeepCellLayerEntryAtPadOffset SldCell.generatorMu padAboveCount 0 1]
  show 0 + entries rowIndex padAboveCount * 1 = entries rowIndex padAboveCount
  rw [mulOneIsSelf (entries rowIndex padAboveCount)]
  exact Nat.zero_add (entries rowIndex padAboveCount)

/-- DELTA PATCH, fresh column: `(M * (wires(p) | delta))(r, p) = M(r, p) + M(r, p + 1)` —
the copied source column is the SUM of the two merged columns, the fusion the fan mirrors. -/
theorem lsaDeepDeltaProductFreshColumn (padAboveCount : Nat) (entries : MatrixEntries)
    (rowIndex : Nat) :
    composeEntries (padAboveCount + 2) entries
        (sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorDelta]))
        rowIndex padAboveCount
      = entries rowIndex padAboveCount + entries rowIndex (padAboveCount + 1) := by
  show (sumBelow (fun middleIndex => entries rowIndex middleIndex
        * sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorDelta])
            middleIndex (padAboveCount + 0)) padAboveCount
      + entries rowIndex padAboveCount
        * sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorDelta])
            (padAboveCount + 0) (padAboveCount + 0))
      + entries rowIndex (padAboveCount + 1)
        * sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorDelta])
            (padAboveCount + 1) (padAboveCount + 0)
    = entries rowIndex padAboveCount + entries rowIndex (padAboveCount + 1)
  rw [lsaDeepCellHeadSumVanishes SldCell.generatorDelta padAboveCount entries rowIndex 0,
    lsaDeepCellLayerEntryAtPadOffset SldCell.generatorDelta padAboveCount 0 0,
    lsaDeepCellLayerEntryAtPadOffset SldCell.generatorDelta padAboveCount 1 0]
  show (0 + entries rowIndex padAboveCount * 1) + entries rowIndex (padAboveCount + 1) * 1
    = entries rowIndex padAboveCount + entries rowIndex (padAboveCount + 1)
  rw [mulOneIsSelf (entries rowIndex padAboveCount),
    mulOneIsSelf (entries rowIndex (padAboveCount + 1)),
    Nat.zero_add (entries rowIndex padAboveCount)]

/-- TAU PATCH, low fresh column: `(M * (wires(p) | tau))(r, p) = M(r, p + 1)`. -/
theorem lsaDeepCrossingProductFreshLowColumn (padAboveCount : Nat) (entries : MatrixEntries)
    (rowIndex : Nat) :
    composeEntries (padAboveCount + 2) entries
        (sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.crossing]))
        rowIndex padAboveCount
      = entries rowIndex (padAboveCount + 1) := by
  show (sumBelow (fun middleIndex => entries rowIndex middleIndex
        * sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.crossing])
            middleIndex (padAboveCount + 0)) padAboveCount
      + entries rowIndex padAboveCount
        * sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.crossing])
            (padAboveCount + 0) (padAboveCount + 0))
      + entries rowIndex (padAboveCount + 1)
        * sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.crossing])
            (padAboveCount + 1) (padAboveCount + 0)
    = entries rowIndex (padAboveCount + 1)
  rw [lsaDeepCellHeadSumVanishes SldCell.crossing padAboveCount entries rowIndex 0,
    lsaDeepCellLayerEntryAtPadOffset SldCell.crossing padAboveCount 0 0,
    lsaDeepCellLayerEntryAtPadOffset SldCell.crossing padAboveCount 1 0]
  show (0 + entries rowIndex padAboveCount * 0) + entries rowIndex (padAboveCount + 1) * 1
    = entries rowIndex (padAboveCount + 1)
  rw [mulOneIsSelf (entries rowIndex (padAboveCount + 1))]
  exact Nat.zero_add (entries rowIndex (padAboveCount + 1))

/-- TAU PATCH, high fresh column: `(M * (wires(p) | tau))(r, p + 1) = M(r, p)`. -/
theorem lsaDeepCrossingProductFreshHighColumn (padAboveCount : Nat) (entries : MatrixEntries)
    (rowIndex : Nat) :
    composeEntries (padAboveCount + 2) entries
        (sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.crossing]))
        rowIndex (padAboveCount + 1)
      = entries rowIndex padAboveCount := by
  show (sumBelow (fun middleIndex => entries rowIndex middleIndex
        * sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.crossing])
            middleIndex (padAboveCount + 1)) padAboveCount
      + entries rowIndex padAboveCount
        * sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.crossing])
            (padAboveCount + 0) (padAboveCount + 1))
      + entries rowIndex (padAboveCount + 1)
        * sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.crossing])
            (padAboveCount + 1) (padAboveCount + 1)
    = entries rowIndex padAboveCount
  rw [lsaDeepCellHeadSumVanishes SldCell.crossing padAboveCount entries rowIndex 1,
    lsaDeepCellLayerEntryAtPadOffset SldCell.crossing padAboveCount 0 1,
    lsaDeepCellLayerEntryAtPadOffset SldCell.crossing padAboveCount 1 1]
  show (0 + entries rowIndex padAboveCount * 1) + entries rowIndex (padAboveCount + 1) * 0
    = entries rowIndex padAboveCount
  rw [mulOneIsSelf (entries rowIndex padAboveCount)]
  show 0 + entries rowIndex padAboveCount + 0 = entries rowIndex padAboveCount
  exact Nat.zero_add (entries rowIndex padAboveCount)

/-! ## The double canonical unfold (the two-fresh-column window) -/

/-- Unfolding the canonical list twice exposes the two newest column fans over the
double-below-padded shorter canonical block. -/
theorem lsaCanonicalDoubleSuccUnfolds (padAboveCount targetArity : Nat)
    (entries : MatrixEntries) :
    lstCanonicalLayerList (padAboveCount + 2) targetArity entries
      = sldAppendLayers
          (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
          (sldAppendLayers
            (sldPadLayersBelow 1
              (lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount)))
            (lstFanLayerList targetArity
              (fun mergeRow => entries mergeRow (padAboveCount + 1)))) := by
  show lstCanonicalLayerList (padAboveCount + 1 + 1) targetArity entries = _
  rw [lstCanonicalSuccUnfolds (padAboveCount + 1) targetArity entries,
    lstCanonicalSuccUnfolds padAboveCount targetArity entries,
    sldPadLayersBelowOfAppend 1
      (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
      (lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount)),
    lstPadLayersBelowCompose 1 1 (lstCanonicalLayerList padAboveCount targetArity entries),
    sldAppendLayersAssoc]

/-! ## Piece (i): the three remaining bottom cores, aligned to absorption shape

Each follows the closed-core recipe: unfold the canonical list, slide the deep cell down
past the shorter canonical block, fire the DECIDED fan core under the padded prefix, refold
through rectangle/column agreement with the fresh-column patches. -/

/-- MU BOTTOM CORE, aligned form: a deep add prepended to the canonical list of the
one-narrower matrix converts to the canonical list of `M * (wires(p) | mu)` — the fan of the
shared column appears TWICE, by the decided `lcoMuFanDuplicationHolds`. -/
theorem lsaMuCellAbsorbsAtBottom (padAboveCount targetArity : Nat) (entries : MatrixEntries) :
    SldAreConvertibleLayers (padAboveCount + 2)
      (sldPadLayer padAboveCount 0 [SldCell.generatorMu]
        :: lstCanonicalLayerList (padAboveCount + 1) targetArity entries)
      (lstCanonicalLayerList (padAboveCount + 2) targetArity
        (composeEntries (padAboveCount + 1) entries
          (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.generatorMu])))) := by
  rw [lstCanonicalSuccUnfolds padAboveCount targetArity entries]
  have muSlides : SldAreConvertibleLayers (padAboveCount + 2)
      (sldPadLayer padAboveCount 0 [SldCell.generatorMu]
        :: sldAppendLayers
            (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
            (lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount)))
      (sldAppendLayers
        (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
        (sldAppendCells
            (sldWireLayerOfArity
              (sldLayersTargetArityFrom padAboveCount
                (lstCanonicalLayerList padAboveCount targetArity entries)))
            [SldCell.generatorMu]
          :: lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount))) :=
    sldLowerLayerSlidesDownPastBlock [SldCell.generatorMu]
      (lstCanonicalLayerList padAboveCount targetArity entries) padAboveCount
      (lstCanonicalLayersAreComposable padAboveCount targetArity entries)
      (lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount))
  rw [lstCanonicalLayersReach padAboveCount targetArity entries] at muSlides
  have reachThroughPads : sldLayersTargetArityFrom (padAboveCount + 2)
      (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
      = targetArity + 2 := by
    have liftedReach := sldPadLayersBelowTargetArityFrom 2
      (lstCanonicalLayerList padAboveCount targetArity entries) padAboveCount
    rw [lstCanonicalLayersReach] at liftedReach
    exact liftedReach
  have coreUnderPrefix : SldAreConvertibleLayers (padAboveCount + 2)
      (sldAppendLayers
        (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
        (sldAppendCells (sldWireLayerOfArity targetArity) [SldCell.generatorMu]
          :: lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount)))
      (sldAppendLayers
        (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
        (sldAppendLayers
          (sldPadLayersBelow 1
            (lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount)))
          (lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount)))) := by
    refine sldConvUnderPrefixList
      (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
      (padAboveCount + 2) _ _ ?_
    rw [reachThroughPads]
    exact lcoMuFanDuplicationHolds targetArity (fun mergeRow => entries mergeRow padAboveCount)
  have muMatrixRefold : lstCanonicalLayerList (padAboveCount + 2) targetArity
      (composeEntries (padAboveCount + 1) entries
        (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.generatorMu])))
      = sldAppendLayers
          (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
          (sldAppendLayers
            (sldPadLayersBelow 1
              (lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount)))
            (lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount))) := by
    rw [lsaCanonicalDoubleSuccUnfolds padAboveCount targetArity
        (composeEntries (padAboveCount + 1) entries
          (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.generatorMu]))),
      lstCanonicalRespectsRectangleAgreement padAboveCount targetArity
        (composeEntries (padAboveCount + 1) entries
          (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.generatorMu])))
        entries
        (fun rowIndex colIndex _ isColInside =>
          lsaProductThroughDeepCellReadsPrefix SldCell.generatorMu padAboveCount entries
            rowIndex colIndex isColInside),
      lstFanRespectsColumnAgreement targetArity
        (fun mergeRow =>
          composeEntries (padAboveCount + 1) entries
            (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.generatorMu]))
            mergeRow padAboveCount)
        (fun mergeRow => entries mergeRow padAboveCount)
        (fun mergeRow _ =>
          lsaDeepMuProductFreshLowColumn padAboveCount entries mergeRow),
      lstFanRespectsColumnAgreement targetArity
        (fun mergeRow =>
          composeEntries (padAboveCount + 1) entries
            (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.generatorMu]))
            mergeRow (padAboveCount + 1))
        (fun mergeRow => entries mergeRow padAboveCount)
        (fun mergeRow _ =>
          lsaDeepMuProductFreshHighColumn padAboveCount entries mergeRow)]
  rw [muMatrixRefold]
  exact SldAreConvertibleLayers.fromTransitivity muSlides coreUnderPrefix

/-- DELTA BOTTOM CORE, aligned form: a deep copy prepended to the canonical list of the
one-wider matrix converts to the canonical list of `M * (wires(p) | delta)` — the two newest
fans fuse into the sum-column fan, by the decided `lcoDeltaFanFusionHolds`. -/
theorem lsaDeltaCellAbsorbsAtBottom (padAboveCount targetArity : Nat)
    (entries : MatrixEntries) :
    SldAreConvertibleLayers (padAboveCount + 1)
      (sldPadLayer padAboveCount 0 [SldCell.generatorDelta]
        :: lstCanonicalLayerList (padAboveCount + 2) targetArity entries)
      (lstCanonicalLayerList (padAboveCount + 1) targetArity
        (composeEntries (padAboveCount + 2) entries
          (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.generatorDelta])))) := by
  rw [lsaCanonicalDoubleSuccUnfolds padAboveCount targetArity entries]
  have deltaSlides : SldAreConvertibleLayers (padAboveCount + 1)
      (sldPadLayer padAboveCount 0 [SldCell.generatorDelta]
        :: sldAppendLayers
            (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
            (sldAppendLayers
              (sldPadLayersBelow 1
                (lstFanLayerList targetArity
                  (fun mergeRow => entries mergeRow padAboveCount)))
              (lstFanLayerList targetArity
                (fun mergeRow => entries mergeRow (padAboveCount + 1)))))
      (sldAppendLayers
        (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
        (sldAppendCells
            (sldWireLayerOfArity
              (sldLayersTargetArityFrom padAboveCount
                (lstCanonicalLayerList padAboveCount targetArity entries)))
            [SldCell.generatorDelta]
          :: sldAppendLayers
              (sldPadLayersBelow 1
                (lstFanLayerList targetArity
                  (fun mergeRow => entries mergeRow padAboveCount)))
              (lstFanLayerList targetArity
                (fun mergeRow => entries mergeRow (padAboveCount + 1))))) :=
    sldLowerLayerSlidesDownPastBlock [SldCell.generatorDelta]
      (lstCanonicalLayerList padAboveCount targetArity entries) padAboveCount
      (lstCanonicalLayersAreComposable padAboveCount targetArity entries)
      (sldAppendLayers
        (sldPadLayersBelow 1
          (lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount)))
        (lstFanLayerList targetArity (fun mergeRow => entries mergeRow (padAboveCount + 1))))
  rw [lstCanonicalLayersReach padAboveCount targetArity entries] at deltaSlides
  have reachThroughPad : sldLayersTargetArityFrom (padAboveCount + 1)
      (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
      = targetArity + 1 := by
    have liftedReach := sldPadLayersBelowTargetArityFrom 1
      (lstCanonicalLayerList padAboveCount targetArity entries) padAboveCount
    rw [lstCanonicalLayersReach] at liftedReach
    exact liftedReach
  have coreUnderPrefix : SldAreConvertibleLayers (padAboveCount + 1)
      (sldAppendLayers
        (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
        (sldAppendCells (sldWireLayerOfArity targetArity) [SldCell.generatorDelta]
          :: sldAppendLayers
              (sldPadLayersBelow 1
                (lstFanLayerList targetArity
                  (fun mergeRow => entries mergeRow padAboveCount)))
              (lstFanLayerList targetArity
                (fun mergeRow => entries mergeRow (padAboveCount + 1)))))
      (sldAppendLayers
        (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
        (lstFanLayerList targetArity
          (fun mergeRow =>
            entries mergeRow padAboveCount + entries mergeRow (padAboveCount + 1)))) := by
    refine sldConvUnderPrefixList
      (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
      (padAboveCount + 1) _ _ ?_
    rw [reachThroughPad]
    exact lcoDeltaFanFusionHolds targetArity
      (fun mergeRow => entries mergeRow padAboveCount)
      (fun mergeRow => entries mergeRow (padAboveCount + 1))
  have deltaMatrixRefold : lstCanonicalLayerList (padAboveCount + 1) targetArity
      (composeEntries (padAboveCount + 2) entries
        (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.generatorDelta])))
      = sldAppendLayers
          (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
          (lstFanLayerList targetArity
            (fun mergeRow =>
              entries mergeRow padAboveCount + entries mergeRow (padAboveCount + 1))) := by
    rw [lstCanonicalSuccUnfolds padAboveCount targetArity
        (composeEntries (padAboveCount + 2) entries
          (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.generatorDelta]))),
      lstCanonicalRespectsRectangleAgreement padAboveCount targetArity
        (composeEntries (padAboveCount + 2) entries
          (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.generatorDelta])))
        entries
        (fun rowIndex colIndex _ isColInside =>
          lsaProductThroughDeepCellReadsPrefix SldCell.generatorDelta padAboveCount entries
            rowIndex colIndex isColInside),
      lstFanRespectsColumnAgreement targetArity
        (fun mergeRow =>
          composeEntries (padAboveCount + 2) entries
            (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.generatorDelta]))
            mergeRow padAboveCount)
        (fun mergeRow =>
          entries mergeRow padAboveCount + entries mergeRow (padAboveCount + 1))
        (fun mergeRow _ =>
          lsaDeepDeltaProductFreshColumn padAboveCount entries mergeRow)]
  rw [deltaMatrixRefold]
  exact SldAreConvertibleLayers.fromTransitivity deltaSlides coreUnderPrefix

/-- CROSSING BOTTOM CORE, aligned form: a deep swap prepended to the canonical list converts
to the canonical list of `M * (wires(p) | tau)` — the two newest fans swap, by the decided
`lcxCrossingTwoFanSwapHolds`. -/
theorem lsaCrossingCellAbsorbsAtBottom (padAboveCount targetArity : Nat)
    (entries : MatrixEntries) :
    SldAreConvertibleLayers (padAboveCount + 2)
      (sldPadLayer padAboveCount 0 [SldCell.crossing]
        :: lstCanonicalLayerList (padAboveCount + 2) targetArity entries)
      (lstCanonicalLayerList (padAboveCount + 2) targetArity
        (composeEntries (padAboveCount + 2) entries
          (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.crossing])))) := by
  rw [lsaCanonicalDoubleSuccUnfolds padAboveCount targetArity entries]
  have crossingSlides : SldAreConvertibleLayers (padAboveCount + 2)
      (sldPadLayer padAboveCount 0 [SldCell.crossing]
        :: sldAppendLayers
            (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
            (sldAppendLayers
              (sldPadLayersBelow 1
                (lstFanLayerList targetArity
                  (fun mergeRow => entries mergeRow padAboveCount)))
              (lstFanLayerList targetArity
                (fun mergeRow => entries mergeRow (padAboveCount + 1)))))
      (sldAppendLayers
        (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
        (sldAppendCells
            (sldWireLayerOfArity
              (sldLayersTargetArityFrom padAboveCount
                (lstCanonicalLayerList padAboveCount targetArity entries)))
            [SldCell.crossing]
          :: sldAppendLayers
              (sldPadLayersBelow 1
                (lstFanLayerList targetArity
                  (fun mergeRow => entries mergeRow padAboveCount)))
              (lstFanLayerList targetArity
                (fun mergeRow => entries mergeRow (padAboveCount + 1))))) :=
    sldLowerLayerSlidesDownPastBlock [SldCell.crossing]
      (lstCanonicalLayerList padAboveCount targetArity entries) padAboveCount
      (lstCanonicalLayersAreComposable padAboveCount targetArity entries)
      (sldAppendLayers
        (sldPadLayersBelow 1
          (lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount)))
        (lstFanLayerList targetArity (fun mergeRow => entries mergeRow (padAboveCount + 1))))
  rw [lstCanonicalLayersReach padAboveCount targetArity entries] at crossingSlides
  have reachThroughPads : sldLayersTargetArityFrom (padAboveCount + 2)
      (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
      = targetArity + 2 := by
    have liftedReach := sldPadLayersBelowTargetArityFrom 2
      (lstCanonicalLayerList padAboveCount targetArity entries) padAboveCount
    rw [lstCanonicalLayersReach] at liftedReach
    exact liftedReach
  have coreUnderPrefix : SldAreConvertibleLayers (padAboveCount + 2)
      (sldAppendLayers
        (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
        (sldAppendCells (sldWireLayerOfArity targetArity) [SldCell.crossing]
          :: sldAppendLayers
              (sldPadLayersBelow 1
                (lstFanLayerList targetArity
                  (fun mergeRow => entries mergeRow padAboveCount)))
              (lstFanLayerList targetArity
                (fun mergeRow => entries mergeRow (padAboveCount + 1)))))
      (sldAppendLayers
        (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
        (sldAppendLayers
          (sldPadLayersBelow 1
            (lstFanLayerList targetArity
              (fun mergeRow => entries mergeRow (padAboveCount + 1))))
          (lstFanLayerList targetArity
            (fun mergeRow => entries mergeRow padAboveCount)))) := by
    refine sldConvUnderPrefixList
      (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
      (padAboveCount + 2) _ _ ?_
    rw [reachThroughPads]
    exact lcxCrossingTwoFanSwapHolds targetArity
      (fun mergeRow => entries mergeRow padAboveCount)
      (fun mergeRow => entries mergeRow (padAboveCount + 1))
  have crossingMatrixRefold : lstCanonicalLayerList (padAboveCount + 2) targetArity
      (composeEntries (padAboveCount + 2) entries
        (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.crossing])))
      = sldAppendLayers
          (sldPadLayersBelow 2 (lstCanonicalLayerList padAboveCount targetArity entries))
          (sldAppendLayers
            (sldPadLayersBelow 1
              (lstFanLayerList targetArity
                (fun mergeRow => entries mergeRow (padAboveCount + 1))))
            (lstFanLayerList targetArity
              (fun mergeRow => entries mergeRow padAboveCount))) := by
    rw [lsaCanonicalDoubleSuccUnfolds padAboveCount targetArity
        (composeEntries (padAboveCount + 2) entries
          (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.crossing]))),
      lstCanonicalRespectsRectangleAgreement padAboveCount targetArity
        (composeEntries (padAboveCount + 2) entries
          (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.crossing])))
        entries
        (fun rowIndex colIndex _ isColInside =>
          lsaProductThroughDeepCellReadsPrefix SldCell.crossing padAboveCount entries
            rowIndex colIndex isColInside),
      lstFanRespectsColumnAgreement targetArity
        (fun mergeRow =>
          composeEntries (padAboveCount + 2) entries
            (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.crossing]))
            mergeRow padAboveCount)
        (fun mergeRow => entries mergeRow (padAboveCount + 1))
        (fun mergeRow _ =>
          lsaDeepCrossingProductFreshLowColumn padAboveCount entries mergeRow),
      lstFanRespectsColumnAgreement targetArity
        (fun mergeRow =>
          composeEntries (padAboveCount + 2) entries
            (sldLayerEntries (sldPadLayer padAboveCount 0 [SldCell.crossing]))
            mergeRow (padAboveCount + 1))
        (fun mergeRow => entries mergeRow padAboveCount)
        (fun mergeRow _ =>
          lsaDeepCrossingProductFreshHighColumn padAboveCount entries mergeRow)]
  rw [crossingMatrixRefold]
  exact SldAreConvertibleLayers.fromTransitivity crossingSlides coreUnderPrefix

/-! ## Piece (ii): the below-pad engine instances and the six-way dispatcher -/

/-- MU ABSORPTION at all pads (below-pad engine instance). -/
theorem lsaMuCellAbsorbs (padAboveCount padBelowCount targetArity : Nat)
    (entries : MatrixEntries) :
    SldAreConvertibleLayers (padAboveCount + (2 + padBelowCount))
      (sldPadLayer padAboveCount padBelowCount [SldCell.generatorMu]
        :: lstCanonicalLayerList (padAboveCount + (1 + padBelowCount)) targetArity entries)
      (lstCanonicalLayerList (padAboveCount + (2 + padBelowCount)) targetArity
        (composeEntries (padAboveCount + (1 + padBelowCount)) entries
          (sldLayerEntries (sldPadLayer padAboveCount padBelowCount [SldCell.generatorMu])))) :=
  lstCellAbsorptionLiftsThroughBelowPads SldCell.generatorMu padAboveCount targetArity entries
    (lsaMuCellAbsorbsAtBottom padAboveCount targetArity entries) padBelowCount

/-- DELTA ABSORPTION at all pads (below-pad engine instance). -/
theorem lsaDeltaCellAbsorbs (padAboveCount padBelowCount targetArity : Nat)
    (entries : MatrixEntries) :
    SldAreConvertibleLayers (padAboveCount + (1 + padBelowCount))
      (sldPadLayer padAboveCount padBelowCount [SldCell.generatorDelta]
        :: lstCanonicalLayerList (padAboveCount + (2 + padBelowCount)) targetArity entries)
      (lstCanonicalLayerList (padAboveCount + (1 + padBelowCount)) targetArity
        (composeEntries (padAboveCount + (2 + padBelowCount)) entries
          (sldLayerEntries
            (sldPadLayer padAboveCount padBelowCount [SldCell.generatorDelta])))) :=
  lstCellAbsorptionLiftsThroughBelowPads SldCell.generatorDelta padAboveCount targetArity
    entries (lsaDeltaCellAbsorbsAtBottom padAboveCount targetArity entries) padBelowCount

/-- CROSSING ABSORPTION at all pads (below-pad engine instance). -/
theorem lsaCrossingCellAbsorbs (padAboveCount padBelowCount targetArity : Nat)
    (entries : MatrixEntries) :
    SldAreConvertibleLayers (padAboveCount + (2 + padBelowCount))
      (sldPadLayer padAboveCount padBelowCount [SldCell.crossing]
        :: lstCanonicalLayerList (padAboveCount + (2 + padBelowCount)) targetArity entries)
      (lstCanonicalLayerList (padAboveCount + (2 + padBelowCount)) targetArity
        (composeEntries (padAboveCount + (2 + padBelowCount)) entries
          (sldLayerEntries (sldPadLayer padAboveCount padBelowCount [SldCell.crossing])))) :=
  lstCellAbsorptionLiftsThroughBelowPads SldCell.crossing padAboveCount targetArity entries
    (lsaCrossingCellAbsorbsAtBottom padAboveCount targetArity entries) padBelowCount

/-- THE SIX-WAY DISPATCHER: EVERY padded single cell absorbs into the canonical form, with
the honest product-matrix target — full cell enumeration, no wildcard. -/
theorem lsaSingleCellAbsorbs (absorbedCell : SldCell)
    (padAboveCount padBelowCount targetArity : Nat) (entries : MatrixEntries) :
    SldAreConvertibleLayers
      (padAboveCount + (sldCellSourceArity absorbedCell + padBelowCount))
      (sldPadLayer padAboveCount padBelowCount [absorbedCell]
        :: lstCanonicalLayerList
            (padAboveCount + (sldCellTargetArity absorbedCell + padBelowCount))
            targetArity entries)
      (lstCanonicalLayerList
        (padAboveCount + (sldCellSourceArity absorbedCell + padBelowCount)) targetArity
        (composeEntries
          (padAboveCount + (sldCellTargetArity absorbedCell + padBelowCount)) entries
          (sldLayerEntries (sldPadLayer padAboveCount padBelowCount [absorbedCell])))) := by
  cases absorbedCell with
  | wire => exact lstWireCellAbsorbs padAboveCount padBelowCount targetArity entries
  | generatorMu => exact lsaMuCellAbsorbs padAboveCount padBelowCount targetArity entries
  | generatorEta => exact lstEtaCellAbsorbs padAboveCount padBelowCount targetArity entries
  | generatorDelta =>
      exact lsaDeltaCellAbsorbs padAboveCount padBelowCount targetArity entries
  | generatorEpsilon =>
      exact lstEpsilonCellAbsorbs padAboveCount padBelowCount targetArity entries
  | crossing => exact lsaCrossingCellAbsorbs padAboveCount padBelowCount targetArity entries

/-! ## Piece (iii): multi-cell layer decomposition into padded single cells

A whole layer `wires(p) | cells` absorbs into the canonical form by recursion on the cell
list: the head cell splits off (`layerSplitTopActsFirst`), the padded tail absorbs by
recursion, the padded head absorbs by the six-way dispatcher, and the two-stage product
refolds into the one-layer product through the congruence's own Mat(N) soundness applied to
the split conversion itself. -/

/-- Source arity of a wire-padded head cell. -/
theorem lsaPaddedHeadSourceArity (headCell : SldCell) (padAboveCount : Nat) :
    sldLayerSourceArity (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
      = padAboveCount + sldCellSourceArity headCell := by
  rw [sldAppendCellsSourceArity, sldWireLayerSourceArity]
  rfl

/-- Target arity of a wire-padded head cell. -/
theorem lsaPaddedHeadTargetArity (headCell : SldCell) (padAboveCount : Nat) :
    sldLayerTargetArity (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
      = padAboveCount + sldCellTargetArity headCell := by
  rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
  rfl

/-- Source arity of the split's merged layer, in right-associated normal form. -/
theorem lsaSplitMergedSourceArity (headCell : SldCell) (tailCells : SldLayer)
    (padAboveCount : Nat) :
    sldLayerSourceArity
        (sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
          tailCells)
      = padAboveCount + (sldCellSourceArity headCell + sldLayerSourceArity tailCells) := by
  rw [sldAppendCellsSourceArity, lsaPaddedHeadSourceArity, Nat.add_assoc]

/-- Target arity of the split's merged layer, in right-associated normal form. -/
theorem lsaSplitMergedTargetArity (headCell : SldCell) (tailCells : SldLayer)
    (padAboveCount : Nat) :
    sldLayerTargetArity
        (sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
          tailCells)
      = padAboveCount + (sldCellTargetArity headCell + sldLayerTargetArity tailCells) := by
  rw [sldAppendCellsTargetArity, lsaPaddedHeadTargetArity, Nat.add_assoc]

/-- THE SPLIT-PRODUCT BRIDGE: the two split stages' layer entries multiply back to the
merged layer's entries, on the boundary rectangle — by the congruence's Mat(N) soundness
applied to the split conversion itself, with the two singleton-denote identity collapses. -/
theorem lsaSplitLayerEntriesBridge (headCell : SldCell) (tailCells : SldLayer)
    (padAboveCount : Nat) (middleIndex colIndex : Nat)
    (isMiddleInside : middleIndex
      < padAboveCount + (sldCellTargetArity headCell + sldLayerTargetArity tailCells))
    (isColInside : colIndex
      < padAboveCount + (sldCellSourceArity headCell + sldLayerSourceArity tailCells)) :
    composeEntries
        (padAboveCount + (sldCellTargetArity headCell + sldLayerSourceArity tailCells))
        (sldLayerEntries
          (sldAppendCells
            (sldWireLayerOfArity (padAboveCount + sldCellTargetArity headCell)) tailCells))
        (sldLayerEntries
          (sldPadLayer padAboveCount (sldLayerSourceArity tailCells) [headCell]))
        middleIndex colIndex
      = sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity padAboveCount) (headCell :: tailCells))
          middleIndex colIndex := by
  have splitConv := SldAreConvertibleLayers.layerSplitTopActsFirst
    (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell]) tailCells []
  have isColInsideSplit : colIndex < sldLayerSourceArity
      (sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
        tailCells) := by
    rw [lsaSplitMergedSourceArity]
    exact isColInside
  have denoteAgree := sldConvertibleLayersDenoteEqualEntries splitConv middleIndex colIndex
    isColInsideSplit
  have isMiddleInsideMerged : middleIndex < sldLayerTargetArity
      (sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
        tailCells) := by
    rw [lsaSplitMergedTargetArity]
    exact isMiddleInside
  have leftCollapse : sldLayersDenote
      [sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
        tailCells] middleIndex colIndex
      = sldLayerEntries
          (sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
            tailCells) middleIndex colIndex :=
    sldProductWithIdentityAfterCollapses
      (sldLayerTargetArity
        (sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
          tailCells))
      (sldLayerEntries
        (sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
          tailCells))
      middleIndex colIndex isMiddleInsideMerged
  have isMiddleInsideSecond : middleIndex < sldLayerTargetArity
      (sldAppendCells
        (sldWireLayerOfArity
          (sldLayerTargetArity
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])))
        tailCells) := by
    rw [sldAppendCellsTargetArity, sldWireLayerTargetArity, lsaPaddedHeadTargetArity,
      Nat.add_assoc]
    exact isMiddleInside
  have rightCollapse : sldLayersDenote
      [sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
          (sldWireLayerOfArity (sldLayerSourceArity tailCells)),
        sldAppendCells
          (sldWireLayerOfArity
            (sldLayerTargetArity
              (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])))
          tailCells] middleIndex colIndex
      = composeEntries
          (sldLayerTargetArity
            (sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
              (sldWireLayerOfArity (sldLayerSourceArity tailCells))))
          (sldLayerEntries
            (sldAppendCells
              (sldWireLayerOfArity
                (sldLayerTargetArity
                  (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])))
              tailCells))
          (sldLayerEntries
            (sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
              (sldWireLayerOfArity (sldLayerSourceArity tailCells))))
          middleIndex colIndex :=
    sldProductRespectsEntryAgreement
      (sldLayerTargetArity
        (sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
          (sldWireLayerOfArity (sldLayerSourceArity tailCells))))
      (sldLayersDenote
        [sldAppendCells
          (sldWireLayerOfArity
            (sldLayerTargetArity
              (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])))
          tailCells])
      (sldLayerEntries
        (sldAppendCells
          (sldWireLayerOfArity
            (sldLayerTargetArity
              (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])))
          tailCells))
      (sldLayerEntries
        (sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
          (sldWireLayerOfArity (sldLayerSourceArity tailCells))))
      (sldLayerEntries
        (sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
          (sldWireLayerOfArity (sldLayerSourceArity tailCells))))
      middleIndex colIndex
      (fun innerMiddle _ =>
        sldProductWithIdentityAfterCollapses
          (sldLayerTargetArity
            (sldAppendCells
              (sldWireLayerOfArity
                (sldLayerTargetArity
                  (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])))
              tailCells))
          (sldLayerEntries
            (sldAppendCells
              (sldWireLayerOfArity
                (sldLayerTargetArity
                  (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])))
              tailCells))
          middleIndex innerMiddle isMiddleInsideSecond)
      (fun _ _ => rfl)
  rw [leftCollapse, rightCollapse] at denoteAgree
  have mergedEq : sldAppendCells
      (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell]) tailCells
      = sldAppendCells (sldWireLayerOfArity padAboveCount) (headCell :: tailCells) :=
    Eq.trans
      (sldAppendCellsAssoc (sldWireLayerOfArity padAboveCount) [headCell] tailCells) rfl
  have firstLayerTargetEq : sldLayerTargetArity
      (sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
        (sldWireLayerOfArity (sldLayerSourceArity tailCells)))
      = padAboveCount + (sldCellTargetArity headCell + sldLayerSourceArity tailCells) := by
    rw [sldAppendCellsTargetArity, sldWireLayerTargetArity, lsaPaddedHeadTargetArity,
      Nat.add_assoc]
  have firstLayerEq : sldAppendCells
      (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
      (sldWireLayerOfArity (sldLayerSourceArity tailCells))
      = sldPadLayer padAboveCount (sldLayerSourceArity tailCells) [headCell] :=
    Eq.trans
      (sldAppendCellsAssoc (sldWireLayerOfArity padAboveCount) [headCell]
        (sldWireLayerOfArity (sldLayerSourceArity tailCells))) rfl
  rw [mergedEq, firstLayerTargetEq, firstLayerEq, lsaPaddedHeadTargetArity] at denoteAgree
  exact denoteAgree.symm

/-- THE ABSORBED-PRODUCTS AGREEMENT: absorbing the padded tail then the padded head produces
the same matrix, on the boundary rectangle, as absorbing the whole layer at once — product
associativity plus the split-product bridge. -/
theorem lsaAbsorbedProductsAgree (headCell : SldCell) (tailCells : SldLayer)
    (padAboveCount : Nat) (baseEntries : MatrixEntries) (rowIndex colIndex : Nat)
    (isColInside : colIndex
      < padAboveCount + (sldCellSourceArity headCell + sldLayerSourceArity tailCells)) :
    composeEntries
        (padAboveCount + (sldCellTargetArity headCell + sldLayerSourceArity tailCells))
        (composeEntries
          (padAboveCount + (sldCellTargetArity headCell + sldLayerTargetArity tailCells))
          baseEntries
          (sldLayerEntries
            (sldAppendCells
              (sldWireLayerOfArity (padAboveCount + sldCellTargetArity headCell)) tailCells)))
        (sldLayerEntries
          (sldPadLayer padAboveCount (sldLayerSourceArity tailCells) [headCell]))
        rowIndex colIndex
      = composeEntries
          (padAboveCount + (sldCellTargetArity headCell + sldLayerTargetArity tailCells))
          baseEntries
          (sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) (headCell :: tailCells)))
          rowIndex colIndex := by
  refine Eq.trans (sldProductAssocEntry
    (padAboveCount + (sldCellTargetArity headCell + sldLayerSourceArity tailCells))
    (padAboveCount + (sldCellTargetArity headCell + sldLayerTargetArity tailCells))
    baseEntries
    (sldLayerEntries
      (sldAppendCells (sldWireLayerOfArity (padAboveCount + sldCellTargetArity headCell))
        tailCells))
    (sldLayerEntries (sldPadLayer padAboveCount (sldLayerSourceArity tailCells) [headCell]))
    rowIndex colIndex).symm ?_
  exact sldProductRespectsEntryAgreement
    (padAboveCount + (sldCellTargetArity headCell + sldLayerTargetArity tailCells))
    baseEntries baseEntries
    (composeEntries
      (padAboveCount + (sldCellTargetArity headCell + sldLayerSourceArity tailCells))
      (sldLayerEntries
        (sldAppendCells (sldWireLayerOfArity (padAboveCount + sldCellTargetArity headCell))
          tailCells))
      (sldLayerEntries (sldPadLayer padAboveCount (sldLayerSourceArity tailCells) [headCell])))
    (sldLayerEntries
      (sldAppendCells (sldWireLayerOfArity padAboveCount) (headCell :: tailCells)))
    rowIndex colIndex
    (fun _ _ => rfl)
    (fun middleIndex isMiddleInside =>
      lsaSplitLayerEntriesBridge headCell tailCells padAboveCount middleIndex colIndex
        isMiddleInside isColInside)

/-- THE MULTI-CELL LAYER ABSORPTION: a whole wire-padded layer prepended to the canonical
list converts to the canonical list of the honest one-layer product matrix — cell recursion
through the split, the tail recursion, and the six-way dispatcher. -/
theorem lsaPaddedLayerAbsorbs : (absorbedCells : SldLayer) ->
    (padAboveCount targetArity : Nat) -> (entries : MatrixEntries) ->
    SldAreConvertibleLayers (padAboveCount + sldLayerSourceArity absorbedCells)
      (sldAppendCells (sldWireLayerOfArity padAboveCount) absorbedCells
        :: lstCanonicalLayerList (padAboveCount + sldLayerTargetArity absorbedCells)
            targetArity entries)
      (lstCanonicalLayerList (padAboveCount + sldLayerSourceArity absorbedCells) targetArity
        (composeEntries (padAboveCount + sldLayerTargetArity absorbedCells) entries
          (sldLayerEntries (sldAppendCells (sldWireLayerOfArity padAboveCount) absorbedCells))))
  | [], padAboveCount, targetArity, entries => by
      rw [sldAppendCellsNilRightIsSelf (sldWireLayerOfArity padAboveCount)]
      show SldAreConvertibleLayers padAboveCount
        (sldWireLayerOfArity padAboveCount
          :: lstCanonicalLayerList padAboveCount targetArity entries)
        (lstCanonicalLayerList padAboveCount targetArity
          (composeEntries padAboveCount entries
            (sldLayerEntries (sldWireLayerOfArity padAboveCount))))
      rw [lstCanonicalRespectsRectangleAgreement padAboveCount targetArity
        (composeEntries padAboveCount entries
          (sldLayerEntries (sldWireLayerOfArity padAboveCount)))
        entries
        (fun rowIndex colIndex _ isColInside =>
          lstProductThroughWireLayerCollapses padAboveCount entries rowIndex colIndex
            isColInside)]
      exact lstWireLayerBeforeChainDeletes padAboveCount
        (lstCanonicalLayerList padAboveCount targetArity entries)
        (lstCanonicalLayersAreComposable padAboveCount targetArity entries)
  | headCell :: tailCells, padAboveCount, targetArity, entries => by
      show SldAreConvertibleLayers
        (padAboveCount + (sldCellSourceArity headCell + sldLayerSourceArity tailCells))
        (sldAppendCells (sldWireLayerOfArity padAboveCount) (headCell :: tailCells)
          :: lstCanonicalLayerList
              (padAboveCount + (sldCellTargetArity headCell + sldLayerTargetArity tailCells))
              targetArity entries)
        (lstCanonicalLayerList
          (padAboveCount + (sldCellSourceArity headCell + sldLayerSourceArity tailCells))
          targetArity
          (composeEntries
            (padAboveCount + (sldCellTargetArity headCell + sldLayerTargetArity tailCells))
            entries
            (sldLayerEntries
              (sldAppendCells (sldWireLayerOfArity padAboveCount) (headCell :: tailCells)))))
      have refold : lstCanonicalLayerList
          (padAboveCount + (sldCellSourceArity headCell + sldLayerSourceArity tailCells))
          targetArity
          (composeEntries
            (padAboveCount + (sldCellTargetArity headCell + sldLayerSourceArity tailCells))
            (composeEntries
              (padAboveCount + (sldCellTargetArity headCell + sldLayerTargetArity tailCells))
              entries
              (sldLayerEntries
                (sldAppendCells
                  (sldWireLayerOfArity (padAboveCount + sldCellTargetArity headCell))
                  tailCells)))
            (sldLayerEntries
              (sldPadLayer padAboveCount (sldLayerSourceArity tailCells) [headCell])))
          = lstCanonicalLayerList
              (padAboveCount + (sldCellSourceArity headCell + sldLayerSourceArity tailCells))
              targetArity
              (composeEntries
                (padAboveCount
                  + (sldCellTargetArity headCell + sldLayerTargetArity tailCells))
                entries
                (sldLayerEntries
                  (sldAppendCells (sldWireLayerOfArity padAboveCount)
                    (headCell :: tailCells)))) :=
        lstCanonicalRespectsRectangleAgreement
          (padAboveCount + (sldCellSourceArity headCell + sldLayerSourceArity tailCells))
          targetArity _ _
          (fun rowIndex colIndex _ isColInside =>
            lsaAbsorbedProductsAgree headCell tailCells padAboveCount entries rowIndex
              colIndex isColInside)
      rw [refold.symm]
      have mergedEq : sldAppendCells (sldWireLayerOfArity padAboveCount)
          (headCell :: tailCells)
          = sldAppendCells
              (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell]) tailCells :=
        (Eq.trans
          (sldAppendCellsAssoc (sldWireLayerOfArity padAboveCount) [headCell] tailCells)
          rfl).symm
      rw [mergedEq]
      have splitStep := SldAreConvertibleLayers.layerSplitTopActsFirst
        (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell]) tailCells
        (lstCanonicalLayerList
          (padAboveCount + (sldCellTargetArity headCell + sldLayerTargetArity tailCells))
          targetArity entries)
      rw [lsaSplitMergedSourceArity headCell tailCells padAboveCount,
        lsaPaddedHeadTargetArity headCell padAboveCount] at splitStep
      have firstLayerEq : sldAppendCells
          (sldAppendCells (sldWireLayerOfArity padAboveCount) [headCell])
          (sldWireLayerOfArity (sldLayerSourceArity tailCells))
          = sldPadLayer padAboveCount (sldLayerSourceArity tailCells) [headCell] :=
        Eq.trans
          (sldAppendCellsAssoc (sldWireLayerOfArity padAboveCount) [headCell]
            (sldWireLayerOfArity (sldLayerSourceArity tailCells))) rfl
      rw [firstLayerEq] at splitStep
      have tailAbsorbs := lsaPaddedLayerAbsorbs tailCells
        (padAboveCount + sldCellTargetArity headCell) targetArity entries
      rw [Nat.add_assoc padAboveCount (sldCellTargetArity headCell)
          (sldLayerTargetArity tailCells),
        Nat.add_assoc padAboveCount (sldCellTargetArity headCell)
          (sldLayerSourceArity tailCells)] at tailAbsorbs
      have prefixTargetEq : sldLayerTargetArity
          (sldPadLayer padAboveCount (sldLayerSourceArity tailCells) [headCell])
          = padAboveCount + (sldCellTargetArity headCell + sldLayerSourceArity tailCells) := by
        rw [sldPadLayerTargetArity]
        rfl
      have wrappedTail : SldAreConvertibleLayers
          (padAboveCount + (sldCellSourceArity headCell + sldLayerSourceArity tailCells))
          (sldPadLayer padAboveCount (sldLayerSourceArity tailCells) [headCell]
            :: sldAppendCells
                (sldWireLayerOfArity (padAboveCount + sldCellTargetArity headCell)) tailCells
            :: lstCanonicalLayerList
                (padAboveCount
                  + (sldCellTargetArity headCell + sldLayerTargetArity tailCells))
                targetArity entries)
          (sldPadLayer padAboveCount (sldLayerSourceArity tailCells) [headCell]
            :: lstCanonicalLayerList
                (padAboveCount
                  + (sldCellTargetArity headCell + sldLayerSourceArity tailCells))
                targetArity
                (composeEntries
                  (padAboveCount
                    + (sldCellTargetArity headCell + sldLayerTargetArity tailCells))
                  entries
                  (sldLayerEntries
                    (sldAppendCells
                      (sldWireLayerOfArity (padAboveCount + sldCellTargetArity headCell))
                      tailCells)))) := by
        refine SldAreConvertibleLayers.underLayerPrefix
          (padAboveCount + (sldCellSourceArity headCell + sldLayerSourceArity tailCells))
          (sldPadLayer padAboveCount (sldLayerSourceArity tailCells) [headCell]) ?_
        rw [prefixTargetEq]
        exact tailAbsorbs
      have headAbsorbs := lsaSingleCellAbsorbs headCell padAboveCount
        (sldLayerSourceArity tailCells) targetArity
        (composeEntries
          (padAboveCount + (sldCellTargetArity headCell + sldLayerTargetArity tailCells))
          entries
          (sldLayerEntries
            (sldAppendCells
              (sldWireLayerOfArity (padAboveCount + sldCellTargetArity headCell))
              tailCells)))
      exact SldAreConvertibleLayers.fromTransitivity splitStep
        (SldAreConvertibleLayers.fromTransitivity wrappedTail headAbsorbs)

/-! ## Piece (v) groundwork: the eta stack and the diagonal gadget dissolution

`canonical(0, t, M)` is the embedded zero-vector diagram; its layer shape is ONE layer of
`t` eta cells.  The identity dissolution walks the canonical builder with tall rectangular
identities whose columns are unit vectors; the fresh source climbs the eta stack through
gadget-zero crossings and dies into the diagonal gadget-one, whose fresh-zero accumulator
input turns it into a copy that the counit kills. -/

/-- The layer of `etaCount` fresh-zero cells. -/
def lsaEtaCells : Nat -> SldLayer
  | 0 => []
  | etaPred + 1 => SldCell.generatorEta :: lsaEtaCells etaPred

/-- Eta stacks grow at the bottom as well: snoc form of the cons growth. -/
theorem lsaEtaCellsSnoc : (etaCount : Nat) ->
    lsaEtaCells (etaCount + 1)
      = sldAppendCells (lsaEtaCells etaCount) [SldCell.generatorEta]
  | 0 => rfl
  | etaPred + 1 =>
      congrArg (fun restCells => SldCell.generatorEta :: restCells) (lsaEtaCellsSnoc etaPred)

/-- An eta stack has no source strands. -/
theorem lsaEtaCellsSourceArity : (etaCount : Nat) ->
    sldLayerSourceArity (lsaEtaCells etaCount) = 0
  | 0 => rfl
  | etaPred + 1 => by
      show 0 + sldLayerSourceArity (lsaEtaCells etaPred) = 0
      rw [lsaEtaCellsSourceArity etaPred]

/-- An eta stack has one target strand per cell. -/
theorem lsaEtaCellsTargetArity : (etaCount : Nat) ->
    sldLayerTargetArity (lsaEtaCells etaCount) = etaCount
  | 0 => rfl
  | etaPred + 1 => by
      show 1 + sldLayerTargetArity (lsaEtaCells etaPred) = etaPred + 1
      rw [lsaEtaCellsTargetArity etaPred]
      exact Nat.add_comm 1 etaPred

/-- THE ZERO-STACK SHAPE: the embedded zero-vector diagram is ONE layer of eta cells (the
zip tensor merges each fresh eta into the same layer). -/
theorem lsaZeroVectorLayersShape : (etaPred : Nat) ->
    (sldOfWireDiagram (zeroVectorDiagram (etaPred + 1))).layers = [lsaEtaCells (etaPred + 1)]
  | 0 => rfl
  | etaPred + 1 => by
      show sldZipLayersWithPads
          (sldTargetArity (sldOfWireDiagram (zeroVectorDiagram (etaPred + 1))))
          (sldTargetArity (sldOfWireDiagram WireDiagram.zeroGen))
          (sldOfWireDiagram (zeroVectorDiagram (etaPred + 1))).layers
          [[SldCell.generatorEta]]
        = [lsaEtaCells (etaPred + 1 + 1)]
      rw [lsaZeroVectorLayersShape etaPred]
      show sldAppendCells (lsaEtaCells (etaPred + 1)) [SldCell.generatorEta]
          :: ([] : List SldLayer)
        = [lsaEtaCells (etaPred + 1 + 1)]
      rw [(lsaEtaCellsSnoc (etaPred + 1)).symm]

/-- The canonical layer list at source zero IS the eta-stack layer (any matrix). -/
theorem lsaCanonicalZeroSourceShape (etaPred : Nat) (entries : MatrixEntries) :
    lstCanonicalLayerList 0 (etaPred + 1) entries = [lsaEtaCells (etaPred + 1)] :=
  lsaZeroVectorLayersShape etaPred

/-- The scale-one tower dissolves: copy, kill one branch by the counit, refill by the unit —
`scale(1) ~ id`. -/
theorem lsaScaleOneDissolves : SldAreConvertibleLayers 1 (lstScaleLayerList 1) [] := by
  rw [lstScaleSuccUnfolds 0, lstScaleZeroLayerShape]
  have counitFires : SldAreConvertibleLayers 1
      ([SldCell.generatorDelta] :: [SldCell.generatorEpsilon, SldCell.wire]
        :: [[SldCell.generatorEta, SldCell.wire], [SldCell.generatorMu]])
      [[SldCell.generatorEta, SldCell.wire], [SldCell.generatorMu]] :=
    SldAreConvertibleLayers.fromCopyLeftCounitRow 0 0
      [[SldCell.generatorEta, SldCell.wire], [SldCell.generatorMu]]
  have unitFires : SldAreConvertibleLayers 1
      ([SldCell.generatorEta, SldCell.wire] :: [[SldCell.generatorMu]]) [] :=
    SldAreConvertibleLayers.fromAddLeftUnitRow 0 0 []
  exact SldAreConvertibleLayers.fromTransitivity counitFires unitFires

/-- The gadget at scale one collapses to its copy/add/swap frame (the scale window
dissolves). -/
theorem lsaGadgetOneCollapses : SldAreConvertibleLayers 2 (lstGadgetLayerList 1)
    [[SldCell.wire, SldCell.generatorDelta], [SldCell.generatorMu, SldCell.wire],
      [SldCell.crossing]] := by
  rw [lstGadgetLayerShape 1]
  have paddedScale := lcoConvPadsWindow lsaScaleOneDissolves 1 1
  have withTail := sldConvAppendsSuffix paddedScale
    [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]
  refine SldAreConvertibleLayers.underLayerPrefix 2
    [SldCell.wire, SldCell.generatorDelta] ?_
  show SldAreConvertibleLayers (1 + (1 + 1))
    (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList 1))
      [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]])
    [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]
  exact withTail

/-- THE DIAGONAL GADGET DISSOLUTION: a fresh zero fed into the ACCUMULATOR input of the
scale-one gadget makes it a bare copy — `(eta | wire) ; gadget(1) ~ delta` (the derivation
`(0, s) -> (s, 0 + 1 * s) = (s, s)`). -/
theorem lsaFreshZeroIntoGadgetOneMakesCopy : SldAreConvertibleLayers 1
    ([SldCell.generatorEta, SldCell.wire] :: lstGadgetLayerList 1)
    [[SldCell.generatorDelta]] := by
  have gadgetReduced : SldAreConvertibleLayers 1
      ([SldCell.generatorEta, SldCell.wire] :: lstGadgetLayerList 1)
      ([SldCell.generatorEta, SldCell.wire]
        :: [[SldCell.wire, SldCell.generatorDelta], [SldCell.generatorMu, SldCell.wire],
            [SldCell.crossing]]) :=
    SldAreConvertibleLayers.underLayerPrefix 1 [SldCell.generatorEta, SldCell.wire]
      lsaGadgetOneCollapses
  have exchangeStep : SldAreConvertibleLayers 1
      ([SldCell.generatorEta, SldCell.wire]
        :: [SldCell.wire, SldCell.generatorDelta]
        :: [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]])
      ([SldCell.generatorDelta]
        :: [SldCell.generatorEta, SldCell.wire, SldCell.wire]
        :: [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]) :=
    sldDisjointLayersExchange [SldCell.generatorEta] [SldCell.generatorDelta]
      [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]
  have unitFires : SldAreConvertibleLayers 2
      ([SldCell.generatorEta, SldCell.wire, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire] :: [[SldCell.crossing]])
      [[SldCell.crossing]] :=
    SldAreConvertibleLayers.fromAddLeftUnitRow 0 1 [[SldCell.crossing]]
  have unitUnderCopy : SldAreConvertibleLayers 1
      ([SldCell.generatorDelta]
        :: [SldCell.generatorEta, SldCell.wire, SldCell.wire]
        :: [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]])
      ([SldCell.generatorDelta] :: [[SldCell.crossing]]) :=
    SldAreConvertibleLayers.underLayerPrefix 1 [SldCell.generatorDelta] unitFires
  have cocommutativityFires : SldAreConvertibleLayers 1
      ([SldCell.generatorDelta] :: [[SldCell.crossing]]) [[SldCell.generatorDelta]] :=
    SldAreConvertibleLayers.fromCopyCocommutativityRow 0 0 []
  exact SldAreConvertibleLayers.fromTransitivity gadgetReduced
    (SldAreConvertibleLayers.fromTransitivity exchangeStep
      (SldAreConvertibleLayers.fromTransitivity unitUnderCopy cocommutativityFires))

/-! ## Piece (v): the identity-form dissolution -/

/-- The wired eta stack: `wireCount` wires above an eta stack, as a layer list — the
canonical form of the tall rectangular identity, and the ruler the dissolution walks. -/
def lsaWiredEtaStack (wireCount : Nat) : Nat -> List SldLayer
  | 0 => []
  | etaDepth + 1 =>
      [sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaDepth + 1))]

/-- An ejected bottom eta layer merges back into the wired eta stack (inverse layer split). -/
theorem lsaWiredEtaStackAbsorbsBottomEta (wireCount : Nat) : (etaDepth : Nat) ->
    SldAreConvertibleLayers (wireCount + 1)
      (sldAppendLayers (lsaWiredEtaStack (wireCount + 1) etaDepth)
        [sldAppendCells (sldWireLayerOfArity (wireCount + (etaDepth + 1)))
          [SldCell.generatorEta]])
      (lsaWiredEtaStack (wireCount + 1) (etaDepth + 1))
  | 0 =>
      SldAreConvertibleLayers.fromReflexivity (wireCount + 1)
        [sldAppendCells (sldWireLayerOfArity (wireCount + (0 + 1))) [SldCell.generatorEta]]
  | etaPred + 1 => by
      have mergeSplit := SldAreConvertibleLayers.layerSplitTopActsFirst
        (sldAppendCells (sldWireLayerOfArity (wireCount + 1)) (lsaEtaCells (etaPred + 1)))
        [SldCell.generatorEta] []
      have mergedStackSource : sldLayerSourceArity
          (sldAppendCells
            (sldAppendCells (sldWireLayerOfArity (wireCount + 1)) (lsaEtaCells (etaPred + 1)))
            [SldCell.generatorEta])
          = wireCount + 1 := by
        rw [sldAppendCellsSourceArity, sldAppendCellsSourceArity, sldWireLayerSourceArity,
          lsaEtaCellsSourceArity]
        rfl
      have etaSingleSource : sldLayerSourceArity [SldCell.generatorEta] = 0 := rfl
      have padZeroEq : sldAppendCells
          (sldAppendCells (sldWireLayerOfArity (wireCount + 1)) (lsaEtaCells (etaPred + 1)))
          (sldWireLayerOfArity 0)
          = sldAppendCells (sldWireLayerOfArity (wireCount + 1)) (lsaEtaCells (etaPred + 1)) :=
        sldAppendCellsNilRightIsSelf
          (sldAppendCells (sldWireLayerOfArity (wireCount + 1)) (lsaEtaCells (etaPred + 1)))
      have mergedWiredTarget : sldLayerTargetArity
          (sldAppendCells (sldWireLayerOfArity (wireCount + 1)) (lsaEtaCells (etaPred + 1)))
          = wireCount + (etaPred + 1 + 1) := by
        rw [sldAppendCellsTargetArity, sldWireLayerTargetArity, lsaEtaCellsTargetArity,
          Nat.succ_add wireCount (etaPred + 1)]
        rfl
      rw [mergedStackSource, etaSingleSource, padZeroEq, mergedWiredTarget] at mergeSplit
      have mergedStackLayerEq : sldAppendCells
          (sldAppendCells (sldWireLayerOfArity (wireCount + 1)) (lsaEtaCells (etaPred + 1)))
          [SldCell.generatorEta]
          = sldAppendCells (sldWireLayerOfArity (wireCount + 1))
              (lsaEtaCells (etaPred + 1 + 1)) := by
        rw [sldAppendCellsAssoc, (lsaEtaCellsSnoc (etaPred + 1)).symm]
      rw [mergedStackLayerEq] at mergeSplit
      exact SldAreConvertibleLayers.fromSymmetry mergeSplit

/-- THE UNIT-COLUMN FAN CLIMB (the genuinely new induction): the wired-eta first stage
followed by the fan of the unit column at the wire boundary converts to the one-deeper wired
eta stack — the fresh source climbs the eta stack by gadget-zero crossings and Neta, and
dies into the diagonal gadget-one whose fresh-zero input makes it a copy that the counit
kills against the zero-column fan's discard. -/
theorem lsaUnitColumnFanClimb : (etaDepth wireCount : Nat) ->
    SldAreConvertibleLayers (wireCount + 1)
      (sldAppendCells
          (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaDepth + 1)))
          (sldWireLayerOfArity 1)
        :: lstFanLayerList (wireCount + (etaDepth + 1))
            (fun mergeRow => identityEntries mergeRow wireCount))
      (lsaWiredEtaStack (wireCount + 1) etaDepth)
  | 0, wireCount => by
      show SldAreConvertibleLayers (wireCount + 1)
        (sldAppendCells
            (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells 1))
            (sldWireLayerOfArity 1)
          :: lstFanLayerList (wireCount + 1)
              (fun mergeRow => identityEntries mergeRow wireCount))
        []
      have firstLayerEq : sldAppendCells
          (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells 1))
          (sldWireLayerOfArity 1)
          = sldAppendCells (sldWireLayerOfArity wireCount)
              [SldCell.generatorEta, SldCell.wire] :=
        Eq.trans (sldAppendCellsAssoc (sldWireLayerOfArity wireCount) (lsaEtaCells 1)
          (sldWireLayerOfArity 1)) rfl
      rw [lstFanSuccUnfolds wireCount (fun mergeRow => identityEntries mergeRow wireCount),
        identityEntryOnDiagonal wireCount,
        lstFanRespectsColumnAgreement wireCount
          (fun mergeRow => identityEntries mergeRow wireCount) (fun _sourceRow => 0)
          (fun mergeRow isRowBelow => identityEntryOffDiagonal (lsaNeOfLt isRowBelow)),
        firstLayerEq]
      have coreWithPads : SldAreConvertibleLayers (wireCount + 1)
          (sldAppendLayers
            (sldPadLayersAbove wireCount
              ([SldCell.generatorEta, SldCell.wire] :: lstGadgetLayerList 1))
            (sldPadLayersBelow 1 (lstFanLayerList wireCount (fun _sourceRow => 0))))
          (sldAppendLayers (sldPadLayersAbove wireCount [[SldCell.generatorDelta]])
            (sldPadLayersBelow 1 (lstFanLayerList wireCount (fun _sourceRow => 0)))) :=
        sldConvAppendsSuffix
          (sldConvPadsAbove lsaFreshZeroIntoGadgetOneMakesCopy wireCount)
          (sldPadLayersBelow 1 (lstFanLayerList wireCount (fun _sourceRow => 0)))
      have discardStep : SldAreConvertibleLayers (wireCount + 1)
          (sldAppendLayers (sldPadLayersAbove wireCount [[SldCell.generatorDelta]])
            (sldPadLayersBelow 1 (lstFanLayerList wireCount (fun _sourceRow => 0))))
          (sldAppendLayers (sldPadLayersAbove wireCount [[SldCell.generatorDelta]])
            (sldPadLayersBelow 1
              [sldAppendCells (sldWireLayerOfArity wireCount)
                [SldCell.generatorEpsilon]])) := by
        refine sldConvUnderPrefixList
          (sldPadLayersAbove wireCount [[SldCell.generatorDelta]]) (wireCount + 1) _ _ ?_
        have prefixReach : sldLayersTargetArityFrom (wireCount + 1)
            (sldPadLayersAbove wireCount [[SldCell.generatorDelta]]) = wireCount + 2 := by
          show sldLayerTargetArity
              (sldAppendCells (sldWireLayerOfArity wireCount) [SldCell.generatorDelta])
            = wireCount + 2
          rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
          rfl
        rw [prefixReach]
        exact sldConvPadsBelow (lstZeroColumnFanIsDiscard wireCount) 1
      have counitStep : SldAreConvertibleLayers (wireCount + 1)
          (sldAppendLayers (sldPadLayersAbove wireCount [[SldCell.generatorDelta]])
            (sldPadLayersBelow 1
              [sldAppendCells (sldWireLayerOfArity wireCount) [SldCell.generatorEpsilon]]))
          [] := by
        have epsilonLayerEq : sldAppendCells
            (sldAppendCells (sldWireLayerOfArity wireCount) [SldCell.generatorEpsilon])
            (sldWireLayerOfArity 1)
            = sldAppendCells (sldWireLayerOfArity wireCount)
                [SldCell.generatorEpsilon, SldCell.wire] :=
          Eq.trans (sldAppendCellsAssoc (sldWireLayerOfArity wireCount)
            [SldCell.generatorEpsilon] (sldWireLayerOfArity 1)) rfl
        show SldAreConvertibleLayers (wireCount + 1)
          (sldAppendCells (sldWireLayerOfArity wireCount) [SldCell.generatorDelta]
            :: [sldAppendCells
                  (sldAppendCells (sldWireLayerOfArity wireCount) [SldCell.generatorEpsilon])
                  (sldWireLayerOfArity 1)])
          []
        rw [epsilonLayerEq]
        exact SldAreConvertibleLayers.fromCopyLeftCounitRow wireCount 0 []
      exact SldAreConvertibleLayers.fromTransitivity coreWithPads
        (SldAreConvertibleLayers.fromTransitivity discardStep counitStep)
  | etaPred + 1, wireCount => by
      show SldAreConvertibleLayers (wireCount + 1)
        (sldAppendCells
            (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1 + 1)))
            (sldWireLayerOfArity 1)
          :: lstFanLayerList (wireCount + (etaPred + 1) + 1)
              (fun mergeRow => identityEntries mergeRow wireCount))
        (lsaWiredEtaStack (wireCount + 1) (etaPred + 1))
      have firstLayerSplitEq : sldAppendCells
          (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1 + 1)))
          (sldWireLayerOfArity 1)
          = sldAppendCells
              (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
              [SldCell.generatorEta, SldCell.wire] := by
        rw [lsaEtaCellsSnoc (etaPred + 1),
          (sldAppendCellsAssoc (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1))
            [SldCell.generatorEta]).symm,
          sldAppendCellsAssoc
            (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
            [SldCell.generatorEta] (sldWireLayerOfArity 1)]
        rfl
      rw [lstFanSuccUnfolds (wireCount + (etaPred + 1))
          (fun mergeRow => identityEntries mergeRow wireCount),
        identityEntryOffDiagonal (lsaNeOfGt (lsaLtAddSucc wireCount etaPred)),
        firstLayerSplitEq]
      have firstLayerTarget : sldLayerTargetArity
          (sldAppendCells
            (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
            [SldCell.generatorEta, SldCell.wire])
          = wireCount + (etaPred + 1) + 2 := by
        rw [sldAppendCellsTargetArity, sldAppendCellsTargetArity, sldWireLayerTargetArity,
          lsaEtaCellsTargetArity]
        rfl
      have crossedUnderFirst : SldAreConvertibleLayers (wireCount + 1)
          (sldAppendCells
              (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
              [SldCell.generatorEta, SldCell.wire]
            :: sldAppendLayers
                (sldPadLayersAbove (wireCount + (etaPred + 1)) (lstGadgetLayerList 0))
                (sldPadLayersBelow 1
                  (lstFanLayerList (wireCount + (etaPred + 1))
                    (fun mergeRow => identityEntries mergeRow wireCount))))
          (sldAppendCells
              (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
              [SldCell.generatorEta, SldCell.wire]
            :: sldAppendLayers
                (sldPadLayersAbove (wireCount + (etaPred + 1)) [[SldCell.crossing]])
                (sldPadLayersBelow 1
                  (lstFanLayerList (wireCount + (etaPred + 1))
                    (fun mergeRow => identityEntries mergeRow wireCount)))) := by
        refine SldAreConvertibleLayers.underLayerPrefix (wireCount + 1)
          (sldAppendCells
            (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
            [SldCell.generatorEta, SldCell.wire]) ?_
        rw [firstLayerTarget]
        exact sldConvAppendsSuffix
          (sldConvPadsAbove lstGadgetZeroConvertsToCrossing (wireCount + (etaPred + 1)))
          (sldPadLayersBelow 1
            (lstFanLayerList (wireCount + (etaPred + 1))
              (fun mergeRow => identityEntries mergeRow wireCount)))
      have firstLayerSource : sldLayerSourceArity
          (sldAppendCells
            (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
            [SldCell.generatorEta, SldCell.wire])
          = wireCount + 1 := by
        rw [sldAppendCellsSourceArity, sldAppendCellsSourceArity, sldWireLayerSourceArity,
          lsaEtaCellsSourceArity]
        rfl
      have etaWireSource : sldLayerSourceArity [SldCell.generatorEta, SldCell.wire] = 1 := rfl
      have wiredEtaTarget : sldLayerTargetArity
          (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
          = wireCount + (etaPred + 1) := by
        rw [sldAppendCellsTargetArity, sldWireLayerTargetArity, lsaEtaCellsTargetArity]
      have splitFirst := SldAreConvertibleLayers.layerSplitTopActsFirst
        (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
        [SldCell.generatorEta, SldCell.wire]
        (sldAppendCells (sldWireLayerOfArity (wireCount + (etaPred + 1))) [SldCell.crossing]
          :: sldPadLayersBelow 1
              (lstFanLayerList (wireCount + (etaPred + 1))
                (fun mergeRow => identityEntries mergeRow wireCount)))
      rw [firstLayerSource, etaWireSource, wiredEtaTarget] at splitFirst
      have splitFirstLayerTarget : sldLayerTargetArity
          (sldAppendCells
            (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
            (sldWireLayerOfArity 1))
          = wireCount + (etaPred + 1) + 1 := by
        rw [sldAppendCellsTargetArity, wiredEtaTarget, sldWireLayerTargetArity]
      have swapUnderFirst : SldAreConvertibleLayers (wireCount + 1)
          (sldAppendCells
              (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
              (sldWireLayerOfArity 1)
            :: sldAppendCells (sldWireLayerOfArity (wireCount + (etaPred + 1)))
                [SldCell.generatorEta, SldCell.wire]
            :: sldAppendCells (sldWireLayerOfArity (wireCount + (etaPred + 1)))
                [SldCell.crossing]
            :: sldPadLayersBelow 1
                (lstFanLayerList (wireCount + (etaPred + 1))
                  (fun mergeRow => identityEntries mergeRow wireCount)))
          (sldAppendCells
              (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
              (sldWireLayerOfArity 1)
            :: sldAppendCells (sldWireLayerOfArity (wireCount + (etaPred + 1)))
                [SldCell.wire, SldCell.generatorEta]
            :: sldPadLayersBelow 1
                (lstFanLayerList (wireCount + (etaPred + 1))
                  (fun mergeRow => identityEntries mergeRow wireCount))) := by
        refine SldAreConvertibleLayers.underLayerPrefix (wireCount + 1)
          (sldAppendCells
            (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
            (sldWireLayerOfArity 1)) ?_
        rw [splitFirstLayerTarget]
        exact SldAreConvertibleLayers.fromSwapPastZeroRow (wireCount + (etaPred + 1)) 0
          (sldPadLayersBelow 1
            (lstFanLayerList (wireCount + (etaPred + 1))
              (fun mergeRow => identityEntries mergeRow wireCount)))
      have slidLayerEq : sldAppendCells (sldWireLayerOfArity (wireCount + (etaPred + 1)))
          [SldCell.wire, SldCell.generatorEta]
          = sldAppendCells (sldWireLayerOfArity (wireCount + (etaPred + 1) + 1))
              [SldCell.generatorEta] := by
        show sldAppendCells (sldWireLayerOfArity (wireCount + (etaPred + 1)))
            (sldAppendCells (sldWireLayerOfArity 1) [SldCell.generatorEta])
          = _
        rw [(sldAppendCellsAssoc (sldWireLayerOfArity (wireCount + (etaPred + 1)))
            (sldWireLayerOfArity 1) [SldCell.generatorEta]).symm,
          sldWireLayerSplitsAtCount (wireCount + (etaPred + 1)) 1]
      rw [slidLayerEq] at swapUnderFirst
      have etaSlides : SldAreConvertibleLayers (wireCount + (etaPred + 1) + 1)
          (sldAppendCells (sldWireLayerOfArity (wireCount + (etaPred + 1) + 1))
              [SldCell.generatorEta]
            :: sldAppendLayers
                (sldPadLayersBelow 1
                  (lstFanLayerList (wireCount + (etaPred + 1))
                    (fun mergeRow => identityEntries mergeRow wireCount)))
                [])
          (sldAppendLayers
            (sldPadLayersBelow 0
              (lstFanLayerList (wireCount + (etaPred + 1))
                (fun mergeRow => identityEntries mergeRow wireCount)))
            (sldAppendCells
                (sldWireLayerOfArity
                  (sldLayersTargetArityFrom (wireCount + (etaPred + 1) + 1)
                    (lstFanLayerList (wireCount + (etaPred + 1))
                      (fun mergeRow => identityEntries mergeRow wireCount))))
                [SldCell.generatorEta]
              :: [])) :=
        sldLowerLayerSlidesDownPastBlock [SldCell.generatorEta]
          (lstFanLayerList (wireCount + (etaPred + 1))
            (fun mergeRow => identityEntries mergeRow wireCount))
          (wireCount + (etaPred + 1) + 1)
          (lstFanLayersAreComposable (wireCount + (etaPred + 1))
            (fun mergeRow => identityEntries mergeRow wireCount))
          []
      rw [sldAppendLayersNilRightIsSelf, sldPadLayersBelowWithZeroIsSelf,
        lstFanLayersReach] at etaSlides
      have slideUnderFirst : SldAreConvertibleLayers (wireCount + 1)
          (sldAppendCells
              (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
              (sldWireLayerOfArity 1)
            :: sldAppendCells (sldWireLayerOfArity (wireCount + (etaPred + 1) + 1))
                [SldCell.generatorEta]
            :: sldPadLayersBelow 1
                (lstFanLayerList (wireCount + (etaPred + 1))
                  (fun mergeRow => identityEntries mergeRow wireCount)))
          (sldAppendCells
              (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
              (sldWireLayerOfArity 1)
            :: sldAppendLayers
                (lstFanLayerList (wireCount + (etaPred + 1))
                  (fun mergeRow => identityEntries mergeRow wireCount))
                (sldAppendCells (sldWireLayerOfArity (wireCount + (etaPred + 1)))
                    [SldCell.generatorEta]
                  :: [])) := by
        refine SldAreConvertibleLayers.underLayerPrefix (wireCount + 1)
          (sldAppendCells
            (sldAppendCells (sldWireLayerOfArity wireCount) (lsaEtaCells (etaPred + 1)))
            (sldWireLayerOfArity 1)) ?_
        rw [splitFirstLayerTarget]
        exact etaSlides
      have recursedWithSuffix := sldConvAppendsSuffix
        (lsaUnitColumnFanClimb etaPred wireCount)
        [sldAppendCells (sldWireLayerOfArity (wireCount + (etaPred + 1)))
          [SldCell.generatorEta]]
      exact SldAreConvertibleLayers.fromTransitivity crossedUnderFirst
        (SldAreConvertibleLayers.fromTransitivity splitFirst
          (SldAreConvertibleLayers.fromTransitivity swapUnderFirst
            (SldAreConvertibleLayers.fromTransitivity slideUnderFirst
              (SldAreConvertibleLayers.fromTransitivity recursedWithSuffix
                (lsaWiredEtaStackAbsorbsBottomEta wireCount etaPred)))))

/-- THE TALL-IDENTITY LADDER: the canonical list of a tall rectangular identity converts to
the wired eta stack — column induction, each step riding the unit-column fan climb. -/
theorem lsaTallIdentityCanonicalConverts : (wireCount etaDepth : Nat) ->
    SldAreConvertibleLayers wireCount
      (lstCanonicalLayerList wireCount (wireCount + etaDepth) identityEntries)
      (lsaWiredEtaStack wireCount etaDepth)
  | 0, etaDepth => by
      rw [Nat.zero_add etaDepth]
      cases etaDepth with
      | zero => exact SldAreConvertibleLayers.fromReflexivity 0 []
      | succ etaPred =>
          rw [lsaCanonicalZeroSourceShape etaPred identityEntries]
          exact SldAreConvertibleLayers.fromReflexivity 0 [lsaEtaCells (etaPred + 1)]
  | wirePred + 1, etaDepth => by
      show SldAreConvertibleLayers (wirePred + 1)
        (lstCanonicalLayerList (wirePred + 1) (wirePred + 1 + etaDepth) identityEntries)
        (lsaWiredEtaStack (wirePred + 1) etaDepth)
      rw [Nat.succ_add wirePred etaDepth,
        lstCanonicalSuccUnfolds wirePred (wirePred + etaDepth + 1) identityEntries]
      have loweredRecursion := sldConvAppendsSuffix
        (sldConvPadsBelow (lsaTallIdentityCanonicalConverts wirePred (etaDepth + 1)) 1)
        (lstFanLayerList (wirePred + etaDepth + 1)
          (fun mergeRow => identityEntries mergeRow wirePred))
      exact SldAreConvertibleLayers.fromTransitivity loweredRecursion
        (lsaUnitColumnFanClimb etaDepth wirePred)

/-- THE IDENTITY-FORM DISSOLUTION: the canonical list of the identity matrix converts to the
EMPTY layer list — the identity diagram's canonical form is no syntax at all. -/
theorem lsaCanonicalOfIdentityDissolves (strandCount : Nat) :
    SldAreConvertibleLayers strandCount
      (lstCanonicalLayerList strandCount strandCount identityEntries) [] :=
  lsaTallIdentityCanonicalConverts strandCount 0

/-! ## Pieces (iv) + (vi): the layer-list induction and THE ASSEMBLY -/

/-- THE CHAIN INDUCTION: every composable layer list converts to the canonical layer list of
its own denotation — nil is the identity-form dissolution, cons wraps the tail recursion
under the head layer and fires the multi-cell layer absorption at pad zero. -/
theorem lsaComposableChainReducesToCanonical : (layers : List SldLayer) ->
    (boundaryArity : Nat) -> sldLayersAreComposableFrom boundaryArity layers = true ->
    SldAreConvertibleLayers boundaryArity layers
      (lstCanonicalLayerList boundaryArity (sldLayersTargetArityFrom boundaryArity layers)
        (sldLayersDenote layers))
  | [], boundaryArity, _ =>
      SldAreConvertibleLayers.fromSymmetry (lsaCanonicalOfIdentityDissolves boundaryArity)
  | headLayer :: tailLayers, boundaryArity, isComposable => by
      have doesHeadMatch : sldLayerSourceArity headLayer = boundaryArity :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isComposable)
      have wrappedTail := SldAreConvertibleLayers.underLayerPrefix boundaryArity headLayer
        (lsaComposableChainReducesToCanonical tailLayers (sldLayerTargetArity headLayer)
          (rightIsTrueOfAndTrue isComposable))
      have absorbed := lsaPaddedLayerAbsorbs headLayer 0
        (sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers)
        (sldLayersDenote tailLayers)
      rw [Nat.zero_add (sldLayerSourceArity headLayer),
        Nat.zero_add (sldLayerTargetArity headLayer), doesHeadMatch] at absorbed
      exact SldAreConvertibleLayers.fromTransitivity wrappedTail absorbed

/-- THE ASSEMBLY: the frozen owner Prop of `StaircaseCompleteness` is INHABITED — every
composable strict-layer diagram converts to the canonical layer list of its own Mat(N)
denotation.  Direct ascription of the verbatim statement. -/
theorem lsaCanonicalReductionHolds : lstCanonicalReductionOverStrictLayersStatement :=
  fun diagram isComposable =>
    lsaComposableChainReducesToCanonical diagram.layers diagram.sourceArity isComposable

/-! ## THE DECISION BICONDITIONAL over `SldDiagram` -/

/-- Well-formed composable diagrams with matching boundaries are convertible IFF their
Mat(N) denotations agree on the boundary rectangle — soundness one way, canonical reduction
through the SHARED canonical form the other. -/
theorem lsaConvertibilityDecidedByDenotation (leftDiagram rightDiagram : SldDiagram)
    (isLeftComposable : sldIsComposable leftDiagram = true)
    (isRightComposable : sldIsComposable rightDiagram = true)
    (doSourcesMatch : rightDiagram.sourceArity = leftDiagram.sourceArity)
    (doTargetsMatch : sldTargetArity rightDiagram = sldTargetArity leftDiagram) :
    Iff
      (SldAreConvertibleLayers leftDiagram.sourceArity leftDiagram.layers
        rightDiagram.layers)
      (doEntriesAgreeUpTo (sldTargetArity leftDiagram) leftDiagram.sourceArity
        (sldDenote leftDiagram) (sldDenote rightDiagram) = true) :=
  Iff.intro
    (fun areConvertible =>
      sldConvertibleLayersDenoteAgreeUpTo areConvertible (sldTargetArity leftDiagram))
    (fun doDenotesAgree => by
      have leftReduces := lsaCanonicalReductionHolds leftDiagram isLeftComposable
      have rightReduces := lsaCanonicalReductionHolds rightDiagram isRightComposable
      rw [doSourcesMatch, doTargetsMatch] at rightReduces
      have canonicalsMatch : lstCanonicalLayerList leftDiagram.sourceArity
          (sldTargetArity leftDiagram) (sldDenote leftDiagram)
          = lstCanonicalLayerList leftDiagram.sourceArity (sldTargetArity leftDiagram)
              (sldDenote rightDiagram) :=
        lstCanonicalRespectsRectangleAgreement leftDiagram.sourceArity
          (sldTargetArity leftDiagram) (sldDenote leftDiagram) (sldDenote rightDiagram)
          (pointwiseOfAgreeUpTo (sldTargetArity leftDiagram) leftDiagram.sourceArity
            (sldDenote leftDiagram) (sldDenote rightDiagram) doDenotesAgree)
      rw [canonicalsMatch] at leftReduces
      exact SldAreConvertibleLayers.fromTransitivity leftReduces
        (SldAreConvertibleLayers.fromSymmetry rightReduces))

/-! ## Fires (small denotes only) and the kernel-rfl negative control -/

/-- CANONICAL-REDUCTION FIRE 1: the doubling diagram (copy then add) reduces end-to-end to
the canonical form of its own denotation. -/
theorem lsaCanonicalReductionFireOnDoubling :
    SldAreConvertibleLayers 1 [[SldCell.generatorDelta], [SldCell.generatorMu]]
      (lstCanonicalLayerList 1 1
        (sldLayersDenote [[SldCell.generatorDelta], [SldCell.generatorMu]])) :=
  lsaCanonicalReductionHolds
    { sourceArity := 1, layers := [[SldCell.generatorDelta], [SldCell.generatorMu]] } rfl

/-- FIRE 1 consumed through soundness: both sides denote the same 1x1 matrix. -/
theorem lsaDoublingFireDenotesEqually :
    doEntriesAgreeUpTo 1 1
      (sldLayersDenote [[SldCell.generatorDelta], [SldCell.generatorMu]])
      (sldLayersDenote
        (lstCanonicalLayerList 1 1
          (sldLayersDenote [[SldCell.generatorDelta], [SldCell.generatorMu]]))) = true :=
  sldConvertibleLayersDenoteAgreeUpTo lsaCanonicalReductionFireOnDoubling 1

/-- CANONICAL-REDUCTION FIRE 2: the bare crossing reduces end-to-end to the canonical form
of the swap matrix. -/
theorem lsaCanonicalReductionFireOnCrossing :
    SldAreConvertibleLayers 2 [[SldCell.crossing]]
      (lstCanonicalLayerList 2 2 (sldLayersDenote [[SldCell.crossing]])) :=
  lsaCanonicalReductionHolds { sourceArity := 2, layers := [[SldCell.crossing]] } rfl

/-- FIRE 2 consumed through soundness: both sides denote the same 2x2 matrix. -/
theorem lsaCrossingFireDenotesEqually :
    doEntriesAgreeUpTo 2 2 (sldLayersDenote [[SldCell.crossing]])
      (sldLayersDenote (lstCanonicalLayerList 2 2 (sldLayersDenote [[SldCell.crossing]])))
      = true :=
  sldConvertibleLayersDenoteAgreeUpTo lsaCanonicalReductionFireOnCrossing 2

/-- IDENTITY-DISSOLUTION FIRE: the main theorem consumed on the empty two-strand diagram. -/
theorem lsaCanonicalReductionFireOnIdentity :
    SldAreConvertibleLayers 2 []
      (lstCanonicalLayerList 2 2 (sldDenote (sldIdentityDiagram 2))) :=
  lsaCanonicalReductionHolds (sldIdentityDiagram 2) rfl

/-- KERNEL-RFL NEGATIVE CONTROL: doubling and closed-loop-zero denote DIFFERENT 1x1
matrices — the completeness machinery did not collapse the semantics. -/
theorem lsaDistinctDenotationsPin :
    doEntriesAgreeUpTo 1 1
      (sldLayersDenote [[SldCell.generatorDelta], [SldCell.generatorMu]])
      (sldLayersDenote [[SldCell.generatorEpsilon], [SldCell.generatorEta]]) = false := rfl

/-- The distinct-denotation pair stays NON-convertible (soundness consumes the pin). -/
theorem lsaDistinctPairStaysNonConvertible :
    SldAreConvertibleLayers 1 [[SldCell.generatorDelta], [SldCell.generatorMu]]
      [[SldCell.generatorEpsilon], [SldCell.generatorEta]] -> False :=
  sldNotConvertibleOfDistinctDenotes [[SldCell.generatorDelta], [SldCell.generatorMu]]
    [[SldCell.generatorEpsilon], [SldCell.generatorEta]] 1 lsaDistinctDenotationsPin

/-! ## THE CONTENT MARKER

`lstCanonicalReductionOverStrictLayersStatement` is INHABITED (`lsaCanonicalReductionHolds`)
and the decision biconditional over `SldDiagram` is derived
(`lsaConvertibilityDecidedByDenotation`).  The frozen owners
`lstCanonicalReductionOverStrictLayersProved` (StaircaseCompleteness) and
`fxLafontStrictLayer_hasCanonicalCompleteness` (StrictLayerEmbedding) stay byte-intact
false in their committed files as history, SUPERSEDED by this marker. -/

/-- Content marker (true): canonical completeness over the strict-layer carrier is PROVEN —
the staircase assembly landed with all six cell absorptions, the multi-cell layer
decomposition, the chain induction, and the identity-form dissolution. -/
def fxLafontStaircase_canonicalCompletenessProven : Bool := true

end FX1Poly.Polygraph.Omega.LafontProp
