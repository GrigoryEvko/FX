import FX1Poly.Polygraph.Omega.LafontProp.StaircaseInvariantGate

/-! # Polygraph/Omega/LafontProp/StaircaseCompleteness — the Lafont staircase over the
strict-layer carrier (LAFONT-REPAIR stage 2 phase 2: CANONICAL FORM + ABSORPTION LADDER)

The invariant gate (`StaircaseInvariantGate`, verdict CLEAN BILL) found no conserved quantity
blocking completeness, so this file starts the staircase proper: convert every composable
`SldDiagram` to a canonical diagram determined by its Mat(N) denotation.

## Stage 1 — the canonical form (REUSE DECISION, documented per commission)

`lstCanonicalLayerList a t M := (sldOfWireDiagram (canonicalDiagramOfEntries a t M)).layers`
REUSES the lane's r2 matrix-to-diagram builder (the column-merge ladder of
`MatrixNormalForm.lean`) through the stage-E embedding, rather than rebuilding a
delta/crossing/mu staircase natively.  Reasons, in order: (i) the builder's soundness
(`canonicalDiagramDenotesEntriesWithin`) and rectangle extensionality
(`canonicalDiagramRespectsRectangleAgreement`) transport along the embedding for free
(`lstCanonicalDenotesEntry` / `lstCanonicalRespectsRectangleAgreement` below); (ii) the
builder recurses on the SOURCE side (one column at a time), which is exactly the side a
peeled layer acts on, so per-cell absorption aligns with the builder's own recursion; (iii)
the ladder needs NO crossing-sorted middle — arbitrary matrices are reached without a sorting
network, so the Coxeter-sorting wall the commission flags never blocks stage 1.

## Stage 2 — per-cell absorption (this file's ladder)

The target family: for each cell kind, `padLayer p q [cell] :: canonical(b, t, M)` converts to
`canonical(a, t, M * sandwich)` where the sandwich is the padded cell's own layer matrix.
Shipped CLOSED in this file:

* THE BELOW-PAD REDUCTION (`lstCellAbsorptionLiftsThroughBelowPads`): generic across all six
  cell kinds — absorption at arbitrary below-pad `q` reduces to absorption at `q = 0` (cell
  touching the freshest strands), by induction on `q` riding the builder's column recursion,
  with the two restriction lemmas of the matrix kit discharging the bookkeeping.
* THE BOTTOM CORES for wire / eta (zero) / epsilon (discard), each a genuine fan interaction:
  the wire layer deletes (`lstWireLayerBeforeChainDeletes`), a fresh zero annihilates the
  whole column fan (`lstFreshZeroAnnihilatesFan` — the source-climb induction through the
  gadget, riding the scale-tower absorption `lstScaleTowerAbsorbsFreshZero`), the zero-column
  fan IS the padded discard (`lstZeroColumnFanIsDiscard` — gadget(0) converts to the bare
  crossing, `lstGadgetZeroConvertsToCrossing`, then the Neps naturality climb).
* CLOSED ABSORPTION THEOREMS at all pads: `lstWireCellAbsorbs`, `lstEtaCellAbsorbs`,
  `lstEpsilonCellAbsorbs` — each stated against the honest matrix target
  `composeEntries b M (sldLayerEntries (sldPadLayer p q [cell]))`.

The remaining three bottom cores (mu, delta, crossing) are NAMED OPEN STATEMENTS
(`lstMuFanDuplicationStatement` / `lstDeltaFanFusionStatement` /
`lstCrossingTwoFanSwapStatement`, owner Bools false) with the exact remaining bill in the
marker section — no wall is claimed: none of them has eaten three genuinely-different failed
attacks yet.  The full canonical-reduction statement over this carrier is named
(`lstCanonicalReductionOverStrictLayersStatement`); the assembly (layer absorption + the
list induction + identity-form dissolution) waits on the three open cores.
`fxLafontStrictLayer_hasCanonicalCompleteness` (in `StrictLayerEmbedding`) is UNTOUCHED and
stays false.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; audit twin with per-decl
`#assert_no_axioms` plus an independent `#print axioms` probe. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.LafontProp

/-! ## Stage 1 — the canonical layer lists (embedded ladder builder) -/

/-- THE CANONICAL LAYER LIST of a `targetArity x sourceArity` matrix: the stage-E embedding
of the r2 column-merge ladder.  Composable from `sourceArity`, reaches `targetArity`,
denotes the matrix on the rectangle (theorems below). -/
def lstCanonicalLayerList (sourceArity targetArity : Nat) (entries : MatrixEntries) :
    List SldLayer :=
  (sldOfWireDiagram (canonicalDiagramOfEntries sourceArity targetArity entries)).layers

/-- The embedded scale tower (`scaleWire`): multiply one strand by a scalar. -/
def lstScaleLayerList (scaleFactor : Nat) : List SldLayer :=
  (sldOfWireDiagram (scaleWire scaleFactor)).layers

/-- The embedded merge rung (`scaleThenSwapGadget`): `[input, source]` to
`[source, input + scale * source]`. -/
def lstGadgetLayerList (scaleFactor : Nat) : List SldLayer :=
  (sldOfWireDiagram (scaleThenSwapGadget scaleFactor)).layers

/-- The embedded column-merge ladder (`mergeColumnFan`): fold one fresh source strand into
`vectorLength` accumulated strands with the column as scale factors. -/
def lstFanLayerList (vectorLength : Nat) (columnEntries : Nat -> Nat) : List SldLayer :=
  (sldOfWireDiagram (mergeColumnFan vectorLength columnEntries)).layers

/-- Zipping against the EMPTY bottom list is below-padding (the tensor-with-one-wire shape
every builder stage produces). -/
theorem lstZipWithEmptyBottomIsPadBelow (topFinalArity bottomFinalArity : Nat) :
    (topLayers : List SldLayer) ->
    sldZipLayersWithPads topFinalArity bottomFinalArity topLayers []
      = sldPadLayersBelow bottomFinalArity topLayers
  | [] => rfl
  | _topHead :: _topTail => rfl

/-! ### Stage-1 bookkeeping: composability, reach, denotation, extensionality -/

/-- The canonical layer list composes from its source arity. -/
theorem lstCanonicalLayersAreComposable (sourceArity targetArity : Nat)
    (entries : MatrixEntries) :
    sldLayersAreComposableFrom sourceArity
      (lstCanonicalLayerList sourceArity targetArity entries) = true :=
  sldOfWireDiagramLayersComposable (canonicalDiagramOfEntries sourceArity targetArity entries)

/-- The canonical layer list reaches its target arity. -/
theorem lstCanonicalLayersReach (sourceArity targetArity : Nat) (entries : MatrixEntries) :
    sldLayersTargetArityFrom sourceArity
      (lstCanonicalLayerList sourceArity targetArity entries) = targetArity :=
  sldOfWireDiagramLayersReach (canonicalDiagramOfEntries sourceArity targetArity entries)

/-- STAGE-1 SOUNDNESS, pointwise: the canonical layer list DENOTES the matrix it was built
from — the embedding bridge composed with the r2 ladder soundness. -/
theorem lstCanonicalDenotesEntry (sourceArity targetArity : Nat) (entries : MatrixEntries)
    (rowIndex colIndex : Nat) (isRowInside : rowIndex < targetArity)
    (isColInside : colIndex < sourceArity) :
    sldLayersDenote (lstCanonicalLayerList sourceArity targetArity entries) rowIndex colIndex
      = entries rowIndex colIndex :=
  (sldOfWireDiagramDenoteEntry (canonicalDiagramOfEntries sourceArity targetArity entries)
      rowIndex colIndex isRowInside isColInside).trans
    (canonicalDiagramDenotesEntriesWithin sourceArity targetArity entries rowIndex colIndex
      isRowInside isColInside)

/-- STAGE-1 SOUNDNESS, Bool form on the full rectangle. -/
theorem lstCanonicalDenoteAgrees (sourceArity targetArity : Nat) (entries : MatrixEntries) :
    doEntriesAgreeUpTo targetArity sourceArity
      (sldLayersDenote (lstCanonicalLayerList sourceArity targetArity entries)) entries
      = true :=
  agreeUpToOfPointwise targetArity sourceArity _ entries
    (fun rowIndex colIndex isRowInside isColInside =>
      lstCanonicalDenotesEntry sourceArity targetArity entries rowIndex colIndex
        isRowInside isColInside)

/-- RECTANGLE EXTENSIONALITY, transported: matrices agreeing on the rectangle give
SYNTACTICALLY EQUAL canonical layer lists. -/
theorem lstCanonicalRespectsRectangleAgreement (sourceArity targetArity : Nat)
    (firstEntries secondEntries : MatrixEntries)
    (agreeOnRectangle : ∀ rowIndex colIndex, rowIndex < targetArity ->
      colIndex < sourceArity -> firstEntries rowIndex colIndex = secondEntries rowIndex colIndex) :
    lstCanonicalLayerList sourceArity targetArity firstEntries
      = lstCanonicalLayerList sourceArity targetArity secondEntries :=
  congrArg (fun diagram => (sldOfWireDiagram diagram).layers)
    (canonicalDiagramRespectsRectangleAgreement sourceArity targetArity firstEntries
      secondEntries agreeOnRectangle)

/-- Fan lists respect column agreement below the vector length (transported). -/
theorem lstFanRespectsColumnAgreement (vectorLength : Nat)
    (firstColumn secondColumn : Nat -> Nat)
    (agreeBelow : ∀ rowIndex, rowIndex < vectorLength ->
      firstColumn rowIndex = secondColumn rowIndex) :
    lstFanLayerList vectorLength firstColumn = lstFanLayerList vectorLength secondColumn :=
  congrArg (fun diagram => (sldOfWireDiagram diagram).layers)
    (mergeColumnFanRespectsColumnAgreement vectorLength firstColumn secondColumn agreeBelow)

/-- The scale tower composes from one strand. -/
theorem lstScaleLayersAreComposable (scaleFactor : Nat) :
    sldLayersAreComposableFrom 1 (lstScaleLayerList scaleFactor) = true :=
  sldOfWireDiagramLayersComposable (scaleWire scaleFactor)

/-- The scale tower reaches one strand. -/
theorem lstScaleLayersReach (scaleFactor : Nat) :
    sldLayersTargetArityFrom 1 (lstScaleLayerList scaleFactor) = 1 :=
  sldOfWireDiagramLayersReach (scaleWire scaleFactor)

/-- The gadget composes from two strands. -/
theorem lstGadgetLayersAreComposable (scaleFactor : Nat) :
    sldLayersAreComposableFrom 2 (lstGadgetLayerList scaleFactor) = true :=
  sldOfWireDiagramLayersComposable (scaleThenSwapGadget scaleFactor)

/-- The gadget reaches two strands. -/
theorem lstGadgetLayersReach (scaleFactor : Nat) :
    sldLayersTargetArityFrom 2 (lstGadgetLayerList scaleFactor) = 2 :=
  sldOfWireDiagramLayersReach (scaleThenSwapGadget scaleFactor)

/-- The fan composes from `vectorLength + 1` strands. -/
theorem lstFanLayersAreComposable (vectorLength : Nat) (columnEntries : Nat -> Nat) :
    sldLayersAreComposableFrom (vectorLength + 1)
      (lstFanLayerList vectorLength columnEntries) = true :=
  sldOfWireDiagramLayersComposable (mergeColumnFan vectorLength columnEntries)

/-- The fan reaches `vectorLength` strands. -/
theorem lstFanLayersReach (vectorLength : Nat) (columnEntries : Nat -> Nat) :
    sldLayersTargetArityFrom (vectorLength + 1)
      (lstFanLayerList vectorLength columnEntries) = vectorLength :=
  sldOfWireDiagramLayersReach (mergeColumnFan vectorLength columnEntries)

/-! ## Plumbing kit: pad composition and pad-window bridges (BEFORE the unfold equations,
which consume them) -/

/-- Below-pads compose: padding below twice is padding below by the sum. -/
theorem lstPadLayersBelowCompose (outerPadCount innerPadCount : Nat) :
    (layers : List SldLayer) ->
    sldPadLayersBelow outerPadCount (sldPadLayersBelow innerPadCount layers)
      = sldPadLayersBelow (innerPadCount + outerPadCount) layers
  | [] => rfl
  | headLayer :: tailLayers => by
      show sldAppendCells (sldAppendCells headLayer (sldWireLayerOfArity innerPadCount))
            (sldWireLayerOfArity outerPadCount)
          :: sldPadLayersBelow outerPadCount (sldPadLayersBelow innerPadCount tailLayers)
        = sldAppendCells headLayer (sldWireLayerOfArity (innerPadCount + outerPadCount))
          :: sldPadLayersBelow (innerPadCount + outerPadCount) tailLayers
      rw [sldAppendCellsAssoc, sldWireLayerSplitsAtCount,
        lstPadLayersBelowCompose outerPadCount innerPadCount tailLayers]

/-- Above-pads compose: padding above twice is padding above by the sum (outer pad lands on
top). -/
theorem lstPadLayersAboveCompose (outerPadCount innerPadCount : Nat) :
    (layers : List SldLayer) ->
    sldPadLayersAbove outerPadCount (sldPadLayersAbove innerPadCount layers)
      = sldPadLayersAbove (outerPadCount + innerPadCount) layers
  | [] => rfl
  | headLayer :: tailLayers => by
      show sldAppendCells (sldWireLayerOfArity outerPadCount)
            (sldAppendCells (sldWireLayerOfArity innerPadCount) headLayer)
          :: sldPadLayersAbove outerPadCount (sldPadLayersAbove innerPadCount tailLayers)
        = sldAppendCells (sldWireLayerOfArity (outerPadCount + innerPadCount)) headLayer
          :: sldPadLayersAbove (outerPadCount + innerPadCount) tailLayers
      rw [(sldAppendCellsAssoc (sldWireLayerOfArity outerPadCount)
          (sldWireLayerOfArity innerPadCount) headLayer).symm,
        sldWireLayerSplitsAtCount,
        lstPadLayersAboveCompose outerPadCount innerPadCount tailLayers]

/-- Below-padding an above-padded window is the two-sided pad window. -/
theorem lstPadBelowOfPadAboveIsPadWindow (padAboveCount padBelowCount : Nat) :
    (windowLayers : List SldLayer) ->
    sldPadLayersBelow padBelowCount (sldPadLayersAbove padAboveCount windowLayers)
      = sldPadWindow padAboveCount padBelowCount windowLayers
  | [] => rfl
  | headLayer :: tailLayers => by
      show sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount) headLayer)
            (sldWireLayerOfArity padBelowCount)
          :: sldPadLayersBelow padBelowCount (sldPadLayersAbove padAboveCount tailLayers)
        = sldPadLayer padAboveCount padBelowCount headLayer
          :: sldPadWindow padAboveCount padBelowCount tailLayers
      rw [sldAppendCellsAssoc,
        lstPadBelowOfPadAboveIsPadWindow padAboveCount padBelowCount tailLayers]
      rfl

/-- Above-padding a below-padded window is the two-sided pad window. -/
theorem lstPadAboveOfPadBelowIsPadWindow (padAboveCount padBelowCount : Nat) :
    (windowLayers : List SldLayer) ->
    sldPadLayersAbove padAboveCount (sldPadLayersBelow padBelowCount windowLayers)
      = sldPadWindow padAboveCount padBelowCount windowLayers
  | [] => rfl
  | headLayer :: tailLayers => by
      show sldAppendCells (sldWireLayerOfArity padAboveCount)
            (sldAppendCells headLayer (sldWireLayerOfArity padBelowCount))
          :: sldPadLayersAbove padAboveCount (sldPadLayersBelow padBelowCount tailLayers)
        = sldPadLayer padAboveCount padBelowCount headLayer
          :: sldPadWindow padAboveCount padBelowCount tailLayers
      rw [lstPadAboveOfPadBelowIsPadWindow padAboveCount padBelowCount tailLayers]
      rfl

/-! ### The unfold equations (the builder's recursion, as layer-list identities) -/

/-- The zero scale tower is discard-then-zero. -/
theorem lstScaleZeroLayerShape :
    lstScaleLayerList 0 = [[SldCell.generatorEpsilon], [SldCell.generatorEta]] := rfl

/-- The successor scale tower: copy, scale the top branch beside a passing wire, add. -/
theorem lstScaleSuccUnfolds (scaleFactorPred : Nat) :
    lstScaleLayerList (scaleFactorPred + 1)
      = sldAppendLayers [[SldCell.generatorDelta]]
          (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
            [[SldCell.generatorMu]]) :=
  congrArg
    (fun stageLayers => sldAppendLayers [[SldCell.generatorDelta]]
      (sldAppendLayers stageLayers [[SldCell.generatorMu]]))
    (lstZipWithEmptyBottomIsPadBelow
      (sldTargetArity (sldOfWireDiagram (scaleWire scaleFactorPred))) 1
      (sldOfWireDiagram (scaleWire scaleFactorPred)).layers)

/-- The gadget's layer shape: `(wire | delta) ; (wire | scale | wire) ; (mu | wire) ; tau`. -/
theorem lstGadgetLayerShape (scaleFactor : Nat) :
    lstGadgetLayerList scaleFactor
      = sldAppendLayers [[SldCell.wire, SldCell.generatorDelta]]
          (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
            [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]) := by
  show sldAppendLayers
      (sldAppendLayers
        (sldAppendLayers [[SldCell.wire, SldCell.generatorDelta]]
          (sldZipLayersWithPads
            (sldTargetArity (sldTensorParallel (sldIdentityDiagram 1)
              (sldOfWireDiagram (scaleWire scaleFactor)))) 1
            (sldPadLayersAbove 1 (sldOfWireDiagram (scaleWire scaleFactor)).layers) []))
        [[SldCell.generatorMu, SldCell.wire]])
      [[SldCell.crossing]]
    = sldAppendLayers [[SldCell.wire, SldCell.generatorDelta]]
        (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
          [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]])
  rw [lstZipWithEmptyBottomIsPadBelow, lstPadBelowOfPadAboveIsPadWindow,
    sldAppendLayersAssoc, sldAppendLayersAssoc]
  exact rfl

/-- The base fan is the lone discard (the spent source dies at the top). -/
theorem lstFanZeroLayerShape (columnEntries : Nat -> Nat) :
    lstFanLayerList 0 columnEntries = [[SldCell.generatorEpsilon]] := rfl

/-- The successor fan: the bottom-two gadget under `vectorLengthPred` passing wires, then the
shorter fan beside a passing wire. -/
theorem lstFanSuccUnfolds (vectorLengthPred : Nat) (columnEntries : Nat -> Nat) :
    lstFanLayerList (vectorLengthPred + 1) columnEntries
      = sldAppendLayers
          (sldPadLayersAbove vectorLengthPred
            (lstGadgetLayerList (columnEntries vectorLengthPred)))
          (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred columnEntries)) :=
  congrArg
    (fun stageLayers => sldAppendLayers
      (sldPadLayersAbove vectorLengthPred (lstGadgetLayerList (columnEntries vectorLengthPred)))
      stageLayers)
    (lstZipWithEmptyBottomIsPadBelow
      (sldTargetArity (sldOfWireDiagram (mergeColumnFan vectorLengthPred columnEntries))) 1
      (sldOfWireDiagram (mergeColumnFan vectorLengthPred columnEntries)).layers)

/-- The successor canonical list: the shorter canonical beside a passing wire, then the fan
of the newest column. -/
theorem lstCanonicalSuccUnfolds (sourceArityPred targetArity : Nat) (entries : MatrixEntries) :
    lstCanonicalLayerList (sourceArityPred + 1) targetArity entries
      = sldAppendLayers
          (sldPadLayersBelow 1 (lstCanonicalLayerList sourceArityPred targetArity entries))
          (lstFanLayerList targetArity (fun mergeRow => entries mergeRow sourceArityPred)) :=
  congrArg
    (fun stageLayers => sldAppendLayers stageLayers
      (lstFanLayerList targetArity (fun mergeRow => entries mergeRow sourceArityPred)))
    (lstZipWithEmptyBottomIsPadBelow
      (sldTargetArity (sldOfWireDiagram
        (canonicalDiagramOfEntries sourceArityPred targetArity entries))) 1
      (sldOfWireDiagram (canonicalDiagramOfEntries sourceArityPred targetArity entries)).layers)

/-! ## Wire-layer deletion (the wire bottom core, and the trailing-wire tool) -/

/-- A trailing full-wire layer after any single layer dies (inverse top-split against the
empty bottom layer). -/
theorem lstTrailingWireLayerDies (frontLayer : SldLayer) :
    SldAreConvertibleLayers (sldLayerSourceArity frontLayer)
      [frontLayer, sldWireLayerOfArity (sldLayerTargetArity frontLayer)] [frontLayer] := by
  have splitInstance : SldAreConvertibleLayers
      (sldLayerSourceArity (sldAppendCells frontLayer []))
      (sldAppendCells frontLayer [] :: ([] : List SldLayer))
      (sldAppendCells frontLayer []
        :: sldAppendCells (sldWireLayerOfArity (sldLayerTargetArity frontLayer)) []
        :: ([] : List SldLayer)) :=
    SldAreConvertibleLayers.layerSplitTopActsFirst frontLayer [] []
  rw [sldAppendCellsNilRightIsSelf frontLayer,
    sldAppendCellsNilRightIsSelf (sldWireLayerOfArity (sldLayerTargetArity frontLayer))]
    at splitInstance
  exact SldAreConvertibleLayers.fromSymmetry splitInstance

/-- A LONE wire layer dissolves into no syntax at all — the gate's dissolution fires,
generalized to every strand count: materialize the eta/eps ghost pair (B4 backward) with the
wire layer as suffix, kill the trailing wire layer after the epsilon layer, and collapse the
pair (B4 forward). -/
theorem lstLoneWireLayerDissolves (strandCount : Nat) :
    SldAreConvertibleLayers strandCount [sldWireLayerOfArity strandCount] [] := by
  have materializeGhostPair : SldAreConvertibleLayers strandCount
      [sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEta],
        sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEpsilon],
        sldWireLayerOfArity strandCount]
      [sldWireLayerOfArity strandCount] :=
    SldAreConvertibleLayers.fromDiscardAfterZeroRow strandCount 0
      [sldWireLayerOfArity strandCount]
  have ghostPairCollapses : SldAreConvertibleLayers strandCount
      [sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEta],
        sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEpsilon]]
      [] :=
    SldAreConvertibleLayers.fromDiscardAfterZeroRow strandCount 0 []
  have trailingWireDies : SldAreConvertibleLayers
      (sldLayerSourceArity
        (sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEpsilon]))
      [sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEpsilon],
        sldWireLayerOfArity
          (sldLayerTargetArity
            (sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEpsilon]))]
      [sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEpsilon]] :=
    lstTrailingWireLayerDies
      (sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEpsilon])
  have epsilonPadTarget :
      sldLayerTargetArity
          (sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEpsilon])
        = strandCount := by
    rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
    exact rfl
  have epsilonPadSource :
      sldLayerSourceArity
          (sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEpsilon])
        = strandCount + 1 := by
    rw [sldAppendCellsSourceArity, sldWireLayerSourceArity]
    exact rfl
  rw [epsilonPadTarget, epsilonPadSource] at trailingWireDies
  have etaPadTarget :
      sldLayerTargetArity
          (sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEta])
        = strandCount + 1 := by
    rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
    exact rfl
  have wireTailKilled : SldAreConvertibleLayers strandCount
      [sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEta],
        sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEpsilon],
        sldWireLayerOfArity strandCount]
      [sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEta],
        sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEpsilon]] := by
    refine SldAreConvertibleLayers.underLayerPrefix strandCount
      (sldAppendCells (sldWireLayerOfArity strandCount) [SldCell.generatorEta]) ?_
    rw [etaPadTarget]
    exact trailingWireDies
  exact SldAreConvertibleLayers.fromTransitivity
    (SldAreConvertibleLayers.fromSymmetry materializeGhostPair)
    (SldAreConvertibleLayers.fromTransitivity wireTailKilled ghostPairCollapses)

/-- A full wire layer in front of ANY composable chain deletes (empty chain: the lone
dissolution; nonempty: the inverse empty-top split). -/
theorem lstWireLayerBeforeChainDeletes (boundaryArity : Nat) :
    (layers : List SldLayer) -> sldLayersAreComposableFrom boundaryArity layers = true ->
    SldAreConvertibleLayers boundaryArity (sldWireLayerOfArity boundaryArity :: layers) layers
  | [], _ => lstLoneWireLayerDissolves boundaryArity
  | headLayer :: tailLayers, isChainComposable => by
      have doesHeadMatch : sldLayerSourceArity headLayer = boundaryArity :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isChainComposable)
      have reducedSplit : SldAreConvertibleLayers (sldLayerSourceArity headLayer)
          (headLayer :: tailLayers)
          (sldWireLayerOfArity (sldLayerSourceArity headLayer) :: headLayer :: tailLayers) :=
        SldAreConvertibleLayers.layerSplitTopActsFirst [] headLayer tailLayers
      rw [doesHeadMatch] at reducedSplit
      exact SldAreConvertibleLayers.fromSymmetry reducedSplit

/-! ## Matrix restriction kit (the extensionality patches for absorption bookkeeping) -/

/-- Multiplying against an appended layer's entries at a column inside the TOP block reads
only the top block: the off-block middle indices hit the bottom-left zero rectangle. -/
theorem lstProductAgainstAppendedLayerRestricts (topCells bottomCells : SldLayer)
    (entries : MatrixEntries) (rowIndex colIndex : Nat)
    (isColInsideTop : colIndex < sldLayerSourceArity topCells) :
    composeEntries (sldLayerTargetArity topCells + sldLayerTargetArity bottomCells) entries
        (sldLayerEntries (sldAppendCells topCells bottomCells)) rowIndex colIndex
      = composeEntries (sldLayerTargetArity topCells) entries (sldLayerEntries topCells)
          rowIndex colIndex := by
  show sumBelow (fun middleIndex => entries rowIndex middleIndex
      * sldLayerEntries (sldAppendCells topCells bottomCells) middleIndex colIndex)
      (sldLayerTargetArity topCells + sldLayerTargetArity bottomCells)
    = sumBelow (fun middleIndex => entries rowIndex middleIndex
        * sldLayerEntries topCells middleIndex colIndex) (sldLayerTargetArity topCells)
  rw [sumBelowSplitsAtBlock]
  have offBlockVanishes : sumBelow (fun offsetIndex =>
      entries rowIndex (sldLayerTargetArity topCells + offsetIndex)
      * sldLayerEntries (sldAppendCells topCells bottomCells)
          (sldLayerTargetArity topCells + offsetIndex) colIndex)
      (sldLayerTargetArity bottomCells) = 0 :=
    sumBelowOfAllZeroIsZero _ (sldLayerTargetArity bottomCells) (fun offsetIndex _ => by
      rw [sldAppendCellsEntriesAsBlocks topCells bottomCells,
        directSumEntryInBottomLeftBlock _ _ offsetIndex isColInsideTop]
      rfl)
  rw [offBlockVanishes, Nat.add_zero]
  exact sumBelowRespectsPointwise _ _ (sldLayerTargetArity topCells)
    (fun middleIndex isMiddleInside => by
      rw [sldAppendCellsEntriesAsBlocks topCells bottomCells,
        directSumEntryInTopBlock _ _ isMiddleInside isColInsideTop])

/-- Multiplying against a wire layer's entries collapses to the plain matrix (the wire layer
IS the identity). -/
theorem lstProductThroughWireLayerCollapses (strandCount : Nat) (entries : MatrixEntries)
    (rowIndex colIndex : Nat) (isColInside : colIndex < strandCount) :
    composeEntries strandCount entries (sldLayerEntries (sldWireLayerOfArity strandCount))
        rowIndex colIndex
      = entries rowIndex colIndex := by
  refine Eq.trans (sldProductRespectsEntryAgreement strandCount entries entries
    (sldLayerEntries (sldWireLayerOfArity strandCount)) identityEntries rowIndex colIndex
    (fun _ _ => rfl)
    (fun middleIndex _ => sldWireLayerEntriesAsIdentity strandCount middleIndex colIndex)) ?_
  exact sldProductWithIdentityBeforeCollapses strandCount entries rowIndex colIndex isColInside

/-- Multiplying against a layer extended by ONE below-pad wire, at the fresh LAST column,
reads the matrix at the layer's target index (the wire passes the fresh strand through). -/
theorem lstProductLastColumnThroughBelowWirePad (topCells : SldLayer)
    (entries : MatrixEntries) (rowIndex : Nat) :
    composeEntries (sldLayerTargetArity topCells + 1) entries
        (sldLayerEntries (sldAppendCells topCells (sldWireLayerOfArity 1))) rowIndex
        (sldLayerSourceArity topCells)
      = entries rowIndex (sldLayerTargetArity topCells) := by
  refine Eq.trans (sumBelowOfSingleSupport
    (fun middleIndex => entries rowIndex middleIndex
      * sldLayerEntries (sldAppendCells topCells (sldWireLayerOfArity 1)) middleIndex
          (sldLayerSourceArity topCells))
    (sldLayerTargetArity topCells + 1) (sldLayerTargetArity topCells)
    (Nat.lt_succ_self (sldLayerTargetArity topCells)) ?_) ?_
  · intro middleIndex isMiddleInBound isMiddleOffSupport
    have isMiddleInTop : middleIndex < sldLayerTargetArity topCells := by
      cases ltOrEqOfLtSucc isMiddleInBound with
      | inl isInTail => exact isInTail
      | inr isAtHead => exact absurd isAtHead isMiddleOffSupport
    show entries rowIndex middleIndex
        * sldLayerEntries (sldAppendCells topCells (sldWireLayerOfArity 1)) middleIndex
            (sldLayerSourceArity topCells) = 0
    have colInTopRight : sldLayerEntries (sldAppendCells topCells (sldWireLayerOfArity 1))
        middleIndex (sldLayerSourceArity topCells) = 0 := by
      have blockForm := sldAppendCellsEntriesAsBlocks topCells (sldWireLayerOfArity 1)
        middleIndex (sldLayerSourceArity topCells + 0)
      rw [directSumEntryInTopRightBlock _ _ 0 isMiddleInTop] at blockForm
      exact blockForm
    rw [colInTopRight]
    exact rfl
  · show entries rowIndex (sldLayerTargetArity topCells)
        * sldLayerEntries (sldAppendCells topCells (sldWireLayerOfArity 1))
            (sldLayerTargetArity topCells) (sldLayerSourceArity topCells)
      = entries rowIndex (sldLayerTargetArity topCells)
    have bottomEntryIsOne : sldLayerEntries (sldAppendCells topCells (sldWireLayerOfArity 1))
        (sldLayerTargetArity topCells) (sldLayerSourceArity topCells)
        = sldLayerEntries (sldWireLayerOfArity 1) 0 0 := by
      have blockForm := sldAppendCellsEntriesAsBlocks topCells (sldWireLayerOfArity 1)
        (sldLayerTargetArity topCells + 0) (sldLayerSourceArity topCells + 0)
      rw [directSumEntryInBottomBlock _ _ 0 0] at blockForm
      exact blockForm
    rw [bottomEntryIsOne]
    exact mulOneIsSelf (entries rowIndex (sldLayerTargetArity topCells))

/-! ## The eta ladder: a fresh zero climbs the builder and annihilates

`0 * s = 0` (scale tower), `(u, 0) -> (0, u)` (gadget), `acc + col * 0 = acc` (fan) — each as
a derived conversion, each an induction riding the corresponding unfold equation. -/

/-- SCALE-ETA: the scale tower absorbs a fresh zero — `eta ; scale(s) ~ eta` (the derivation
`s * 0 = 0`).  Induction on the tower: the zero tower is the B4 ghost pair; the successor
tower fires B2 (copy the zero), splits the pair, slides one zero past the shorter tower,
kills it against `mu` by M3, and recurses on the other. -/
theorem lstScaleTowerAbsorbsFreshZero : (scaleFactor : Nat) ->
    SldAreConvertibleLayers 0
      ([SldCell.generatorEta] :: lstScaleLayerList scaleFactor)
      [[SldCell.generatorEta]]
  | 0 => SldAreConvertibleLayers.fromDiscardAfterZeroRow 0 0 [[SldCell.generatorEta]]
  | scaleFactorPred + 1 => by
      rw [lstScaleSuccUnfolds scaleFactorPred]
      have copyFires : SldAreConvertibleLayers 0
          ([SldCell.generatorEta] :: [SldCell.generatorDelta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu]])
          ([SldCell.generatorEta, SldCell.generatorEta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu]]) :=
        SldAreConvertibleLayers.fromCopyAfterZeroRow 0 0
          (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
            [[SldCell.generatorMu]])
      have zeroPairSplits : SldAreConvertibleLayers 0
          ([SldCell.generatorEta, SldCell.generatorEta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu]])
          ([SldCell.generatorEta] :: [SldCell.wire, SldCell.generatorEta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu]]) :=
        SldAreConvertibleLayers.layerSplitTopActsFirst [SldCell.generatorEta]
          [SldCell.generatorEta]
          (sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
            [[SldCell.generatorMu]])
      have etaSlidesPastScale : SldAreConvertibleLayers 1
          ([SldCell.wire, SldCell.generatorEta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu]])
          (sldAppendLayers (sldPadLayersBelow 0 (lstScaleLayerList scaleFactorPred))
            (sldAppendCells
                (sldWireLayerOfArity
                  (sldLayersTargetArityFrom 1 (lstScaleLayerList scaleFactorPred)))
                [SldCell.generatorEta]
              :: [[SldCell.generatorMu]])) :=
        sldLowerLayerSlidesDownPastBlock [SldCell.generatorEta]
          (lstScaleLayerList scaleFactorPred) 1 (lstScaleLayersAreComposable scaleFactorPred)
          [[SldCell.generatorMu]]
      rw [sldPadLayersBelowWithZeroIsSelf, lstScaleLayersReach] at etaSlidesPastScale
      have unitKillsInnerZero : SldAreConvertibleLayers 1
          (sldAppendLayers (lstScaleLayerList scaleFactorPred)
            ([SldCell.wire, SldCell.generatorEta] :: [[SldCell.generatorMu]]))
          (sldAppendLayers (lstScaleLayerList scaleFactorPred) []) := by
        refine sldConvUnderPrefixList (lstScaleLayerList scaleFactorPred) 1
          ([SldCell.wire, SldCell.generatorEta] :: [[SldCell.generatorMu]]) [] ?_
        rw [lstScaleLayersReach]
        exact SldAreConvertibleLayers.fromAddRightUnitRow 0 0 []
      rw [sldAppendLayersNilRightIsSelf] at unitKillsInnerZero
      have innerChain : SldAreConvertibleLayers 1
          ([SldCell.wire, SldCell.generatorEta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu]])
          (lstScaleLayerList scaleFactorPred) :=
        SldAreConvertibleLayers.fromTransitivity etaSlidesPastScale unitKillsInnerZero
      have wrappedInner : SldAreConvertibleLayers 0
          ([SldCell.generatorEta] :: [SldCell.wire, SldCell.generatorEta]
            :: sldAppendLayers (sldPadLayersBelow 1 (lstScaleLayerList scaleFactorPred))
                [[SldCell.generatorMu]])
          ([SldCell.generatorEta] :: lstScaleLayerList scaleFactorPred) :=
        SldAreConvertibleLayers.underLayerPrefix 0 [SldCell.generatorEta] innerChain
      exact SldAreConvertibleLayers.fromTransitivity copyFires
        (SldAreConvertibleLayers.fromTransitivity zeroPairSplits
          (SldAreConvertibleLayers.fromTransitivity wrappedInner
            (lstScaleTowerAbsorbsFreshZero scaleFactorPred)))

/-- GADGET-ETA: the merge gadget absorbs a fresh zero on its SOURCE strand and re-emits it on
the top output — `(wire | eta) ; gadget(s) ~ eta | wire` (the derivation
`(u, 0) -> (0, u + s*0) = (0, u)`).  B2 copies the zero, one copy dies in the scale tower
(SCALE-ETA), the other rides the Neta naturality through `mu` (M3) and `tau` (S1). -/
theorem lstGadgetAbsorbsFreshZero (scaleFactor : Nat) :
    SldAreConvertibleLayers 1
      ([SldCell.wire, SldCell.generatorEta] :: lstGadgetLayerList scaleFactor)
      [[SldCell.generatorEta, SldCell.wire]] := by
  rw [lstGadgetLayerShape scaleFactor]
  have copyFires : SldAreConvertibleLayers 1
      ([SldCell.wire, SldCell.generatorEta] :: [SldCell.wire, SldCell.generatorDelta]
        :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
            [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]])
      ([SldCell.wire, SldCell.generatorEta, SldCell.generatorEta]
        :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
            [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]) :=
    SldAreConvertibleLayers.fromCopyAfterZeroRow 1 0
      (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
        [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]])
  have zeroPairSplits : SldAreConvertibleLayers 1
      ([SldCell.wire, SldCell.generatorEta, SldCell.generatorEta]
        :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
            [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]])
      ([SldCell.wire, SldCell.generatorEta]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorEta]
        :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
            [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]) :=
    SldAreConvertibleLayers.layerSplitTopActsFirst [SldCell.wire, SldCell.generatorEta]
      [SldCell.generatorEta]
      (sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
        [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]])
  have blockIsComposable :
      sldLayersAreComposableFrom 2 (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
        = true :=
    sldPadLayersAboveAreComposableFrom 1 (lstScaleLayerList scaleFactor) 1
      (lstScaleLayersAreComposable scaleFactor)
  have blockReach :
      sldLayersTargetArityFrom 2 (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor)) = 2 := by
    have liftedReach := sldPadLayersAboveTargetArityFrom 1 (lstScaleLayerList scaleFactor) 1
    rw [lstScaleLayersReach] at liftedReach
    exact liftedReach
  have etaSlidesPastBlock : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.wire, SldCell.generatorEta]
        :: sldAppendLayers
            (sldPadLayersBelow 1 (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor)))
            [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]])
      (sldAppendLayers (sldPadLayersBelow 0 (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor)))
        (sldAppendCells
            (sldWireLayerOfArity
              (sldLayersTargetArityFrom 2 (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))))
            [SldCell.generatorEta]
          :: [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]])) :=
    sldLowerLayerSlidesDownPastBlock [SldCell.generatorEta]
      (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor)) 2 blockIsComposable
      [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]
  rw [sldPadLayersBelowWithZeroIsSelf, blockReach,
    lstPadBelowOfPadAboveIsPadWindow 1 1 (lstScaleLayerList scaleFactor)] at etaSlidesPastBlock
  have muEtaExchange : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.wire, SldCell.generatorEta]
        :: [SldCell.generatorMu, SldCell.wire] :: [[SldCell.crossing]])
      ([SldCell.generatorMu] :: [SldCell.wire, SldCell.generatorEta] :: [[SldCell.crossing]]) :=
    SldAreConvertibleLayers.fromSymmetry
      (sldDisjointLayersExchange [SldCell.generatorMu] [SldCell.generatorEta]
        [[SldCell.crossing]])
  have netaBackward : SldAreConvertibleLayers 1
      [[SldCell.wire, SldCell.generatorEta]]
      [[SldCell.generatorEta, SldCell.wire], [SldCell.crossing]] :=
    SldAreConvertibleLayers.fromSymmetry
      (SldAreConvertibleLayers.fromSwapPastZeroRow 0 0 [])
  have netaWithCrossing : SldAreConvertibleLayers 1
      [[SldCell.wire, SldCell.generatorEta], [SldCell.crossing]]
      [[SldCell.generatorEta, SldCell.wire], [SldCell.crossing], [SldCell.crossing]] :=
    sldConvAppendsSuffix netaBackward [[SldCell.crossing]]
  have involutionKillsCrossings : SldAreConvertibleLayers 1
      [[SldCell.generatorEta, SldCell.wire], [SldCell.crossing], [SldCell.crossing]]
      [[SldCell.generatorEta, SldCell.wire]] :=
    SldAreConvertibleLayers.underLayerPrefix 1 [SldCell.generatorEta, SldCell.wire]
      (SldAreConvertibleLayers.fromSwapInvolutionRow 0 0 [])
  have netaChain : SldAreConvertibleLayers 1
      [[SldCell.wire, SldCell.generatorEta], [SldCell.crossing]]
      [[SldCell.generatorEta, SldCell.wire]] :=
    SldAreConvertibleLayers.fromTransitivity netaWithCrossing involutionKillsCrossings
  have muWrappedNeta : SldAreConvertibleLayers 2
      ([SldCell.generatorMu] :: [SldCell.wire, SldCell.generatorEta] :: [[SldCell.crossing]])
      ([SldCell.generatorMu] :: [[SldCell.generatorEta, SldCell.wire]]) :=
    SldAreConvertibleLayers.underLayerPrefix 2 [SldCell.generatorMu] netaChain
  have innerAfterBlock : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.wire, SldCell.generatorEta]
        :: [SldCell.generatorMu, SldCell.wire] :: [[SldCell.crossing]])
      ([SldCell.generatorMu] :: [[SldCell.generatorEta, SldCell.wire]]) :=
    SldAreConvertibleLayers.fromTransitivity muEtaExchange muWrappedNeta
  have underBlock : SldAreConvertibleLayers 2
      (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
        ([SldCell.wire, SldCell.wire, SldCell.generatorEta]
          :: [SldCell.generatorMu, SldCell.wire] :: [[SldCell.crossing]]))
      (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
        ([SldCell.generatorMu] :: [[SldCell.generatorEta, SldCell.wire]])) := by
    refine sldConvUnderPrefixList (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor)) 2 _ _ ?_
    rw [blockReach]
    exact innerAfterBlock
  have innerFull : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.wire, SldCell.generatorEta]
        :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
            [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]])
      (sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
        ([SldCell.generatorMu] :: [[SldCell.generatorEta, SldCell.wire]])) :=
    SldAreConvertibleLayers.fromTransitivity etaSlidesPastBlock underBlock
  have outerWrapped : SldAreConvertibleLayers 1
      ([SldCell.wire, SldCell.generatorEta]
        :: [SldCell.wire, SldCell.wire, SldCell.generatorEta]
        :: sldAppendLayers (sldPadWindow 1 1 (lstScaleLayerList scaleFactor))
            [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]])
      ([SldCell.wire, SldCell.generatorEta]
        :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
            [[SldCell.generatorMu], [SldCell.generatorEta, SldCell.wire]]) :=
    SldAreConvertibleLayers.underLayerPrefix 1 [SldCell.wire, SldCell.generatorEta] innerFull
  have paddedScaleEta : SldAreConvertibleLayers 1
      (sldPadLayersAbove 1 ([SldCell.generatorEta] :: lstScaleLayerList scaleFactor))
      (sldPadLayersAbove 1 [[SldCell.generatorEta]]) :=
    sldConvPadsAbove (lstScaleTowerAbsorbsFreshZero scaleFactor) 1
  have scaleEtaWithSuffix : SldAreConvertibleLayers 1
      ([SldCell.wire, SldCell.generatorEta]
        :: sldAppendLayers (sldPadLayersAbove 1 (lstScaleLayerList scaleFactor))
            [[SldCell.generatorMu], [SldCell.generatorEta, SldCell.wire]])
      ([SldCell.wire, SldCell.generatorEta]
        :: [SldCell.generatorMu] :: [[SldCell.generatorEta, SldCell.wire]]) :=
    sldConvAppendsSuffix paddedScaleEta
      [[SldCell.generatorMu], [SldCell.generatorEta, SldCell.wire]]
  have unitFires : SldAreConvertibleLayers 1
      ([SldCell.wire, SldCell.generatorEta]
        :: [SldCell.generatorMu] :: [[SldCell.generatorEta, SldCell.wire]])
      [[SldCell.generatorEta, SldCell.wire]] :=
    SldAreConvertibleLayers.fromAddRightUnitRow 0 0 [[SldCell.generatorEta, SldCell.wire]]
  exact SldAreConvertibleLayers.fromTransitivity copyFires
    (SldAreConvertibleLayers.fromTransitivity zeroPairSplits
      (SldAreConvertibleLayers.fromTransitivity outerWrapped
        (SldAreConvertibleLayers.fromTransitivity scaleEtaWithSuffix unitFires)))

/-- FRESH-ZERO ANNIHILATES THE FAN: a fresh zero source dies through the whole column-merge
ladder — `(wires(t) | eta) ; fan(t, col) ~ id` (the derivation `acc_i + col_i * 0 = acc_i`).
Source-climb induction: each rung is the padded GADGET-ETA, the base is the B4 ghost pair. -/
theorem lstFreshZeroAnnihilatesFan : (vectorLength : Nat) -> (columnEntries : Nat -> Nat) ->
    SldAreConvertibleLayers vectorLength
      (sldAppendCells (sldWireLayerOfArity vectorLength) [SldCell.generatorEta]
        :: lstFanLayerList vectorLength columnEntries)
      []
  | 0, _columnEntries => SldAreConvertibleLayers.fromDiscardAfterZeroRow 0 0 []
  | vectorLengthPred + 1, columnEntries => by
      rw [lstFanSuccUnfolds vectorLengthPred columnEntries]
      have firstLayerEq :
          sldAppendCells (sldWireLayerOfArity (vectorLengthPred + 1)) [SldCell.generatorEta]
            = sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                [SldCell.wire, SldCell.generatorEta] := by
        rw [(sldWireLayerSplitsAtCount vectorLengthPred 1).symm, sldAppendCellsAssoc]
        exact rfl
      rw [firstLayerEq]
      have paddedGadgetEta : SldAreConvertibleLayers (vectorLengthPred + 1)
          (sldPadLayersAbove vectorLengthPred
            ([SldCell.wire, SldCell.generatorEta]
              :: lstGadgetLayerList (columnEntries vectorLengthPred)))
          (sldPadLayersAbove vectorLengthPred [[SldCell.generatorEta, SldCell.wire]]) :=
        sldConvPadsAbove (lstGadgetAbsorbsFreshZero (columnEntries vectorLengthPred))
          vectorLengthPred
      have gadgetEtaWithSuffix : SldAreConvertibleLayers (vectorLengthPred + 1)
          (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
              [SldCell.wire, SldCell.generatorEta]
            :: sldAppendLayers
                (sldPadLayersAbove vectorLengthPred
                  (lstGadgetLayerList (columnEntries vectorLengthPred)))
                (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred columnEntries)))
          (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
              [SldCell.generatorEta, SldCell.wire]
            :: sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred columnEntries)) :=
        sldConvAppendsSuffix paddedGadgetEta
          (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred columnEntries))
      have secondLayerEq :
          sldAppendCells (sldWireLayerOfArity vectorLengthPred)
              [SldCell.generatorEta, SldCell.wire]
            = sldAppendCells
                (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                  [SldCell.generatorEta])
                (sldWireLayerOfArity 1) :=
        (sldAppendCellsAssoc (sldWireLayerOfArity vectorLengthPred) [SldCell.generatorEta]
          (sldWireLayerOfArity 1)).symm
      rw [secondLayerEq] at gadgetEtaWithSuffix
      have paddedRecursion : SldAreConvertibleLayers (vectorLengthPred + 1)
          (sldPadLayersBelow 1
            (sldAppendCells (sldWireLayerOfArity vectorLengthPred) [SldCell.generatorEta]
              :: lstFanLayerList vectorLengthPred columnEntries))
          (sldPadLayersBelow 1 []) :=
        sldConvPadsBelow (lstFreshZeroAnnihilatesFan vectorLengthPred columnEntries) 1
      exact SldAreConvertibleLayers.fromTransitivity gadgetEtaWithSuffix paddedRecursion

/-! ## The epsilon ladder: the zero-column fan IS the padded discard -/

/-- GADGET-ZERO IS THE CROSSING: `gadget(0) ~ tau` — the scale-0 tower's discard eats the
copy (C2), its zero dies into the add (M3), leaving the bare crossing. -/
theorem lstGadgetZeroConvertsToCrossing :
    SldAreConvertibleLayers 2 (lstGadgetLayerList 0) [[SldCell.crossing]] := by
  rw [lstGadgetLayerShape 0]
  have counitFires : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorDelta]
        :: [SldCell.wire, SldCell.generatorEpsilon, SldCell.wire]
        :: [[SldCell.wire, SldCell.generatorEta, SldCell.wire],
            [SldCell.generatorMu, SldCell.wire], [SldCell.crossing]])
      [[SldCell.wire, SldCell.generatorEta, SldCell.wire],
        [SldCell.generatorMu, SldCell.wire], [SldCell.crossing]] :=
    SldAreConvertibleLayers.fromCopyLeftCounitRow 1 0
      [[SldCell.wire, SldCell.generatorEta, SldCell.wire],
        [SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]
  have unitFires : SldAreConvertibleLayers 2
      ([SldCell.wire, SldCell.generatorEta, SldCell.wire]
        :: [SldCell.generatorMu, SldCell.wire] :: [[SldCell.crossing]])
      [[SldCell.crossing]] :=
    SldAreConvertibleLayers.fromAddRightUnitRow 0 1 [[SldCell.crossing]]
  exact SldAreConvertibleLayers.fromTransitivity counitFires unitFires

/-- THE ZERO-COLUMN FAN IS THE PADDED DISCARD: `fan(t, all-zero) ~ wires(t) | epsilon` — the
gadget rungs collapse to crossings (GADGET-ZERO), and the source strand walks to the top
where the base discard eats it, one Neps naturality per level. -/
theorem lstZeroColumnFanIsDiscard : (vectorLength : Nat) ->
    SldAreConvertibleLayers (vectorLength + 1)
      (lstFanLayerList vectorLength (fun _sourceRow => 0))
      [sldAppendCells (sldWireLayerOfArity vectorLength) [SldCell.generatorEpsilon]]
  | 0 => SldAreConvertibleLayers.fromReflexivity 1 [[SldCell.generatorEpsilon]]
  | vectorLengthPred + 1 => by
      rw [lstFanSuccUnfolds vectorLengthPred (fun _sourceRow => 0)]
      have paddedGadgetZero : SldAreConvertibleLayers (vectorLengthPred + 2)
          (sldPadLayersAbove vectorLengthPred (lstGadgetLayerList 0))
          (sldPadLayersAbove vectorLengthPred [[SldCell.crossing]]) :=
        sldConvPadsAbove lstGadgetZeroConvertsToCrossing vectorLengthPred
      have gadgetZeroWithSuffix : SldAreConvertibleLayers (vectorLengthPred + 2)
          (sldAppendLayers (sldPadLayersAbove vectorLengthPred (lstGadgetLayerList 0))
            (sldPadLayersBelow 1
              (lstFanLayerList vectorLengthPred (fun _sourceRow => 0))))
          (sldAppendCells (sldWireLayerOfArity vectorLengthPred) [SldCell.crossing]
            :: sldPadLayersBelow 1
                (lstFanLayerList vectorLengthPred (fun _sourceRow => 0))) :=
        sldConvAppendsSuffix paddedGadgetZero
          (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred (fun _sourceRow => 0)))
      have crossingPrefixTarget :
          sldLayerTargetArity
              (sldAppendCells (sldWireLayerOfArity vectorLengthPred) [SldCell.crossing])
            = vectorLengthPred + 2 := by
        rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
        exact rfl
      have paddedRecursion : SldAreConvertibleLayers (vectorLengthPred + 2)
          (sldPadLayersBelow 1 (lstFanLayerList vectorLengthPred (fun _sourceRow => 0)))
          (sldPadLayersBelow 1
            [sldAppendCells (sldWireLayerOfArity vectorLengthPred)
              [SldCell.generatorEpsilon]]) :=
        sldConvPadsBelow (lstZeroColumnFanIsDiscard vectorLengthPred) 1
      have recursionUnderCrossing : SldAreConvertibleLayers (vectorLengthPred + 2)
          (sldAppendCells (sldWireLayerOfArity vectorLengthPred) [SldCell.crossing]
            :: sldPadLayersBelow 1
                (lstFanLayerList vectorLengthPred (fun _sourceRow => 0)))
          (sldAppendCells (sldWireLayerOfArity vectorLengthPred) [SldCell.crossing]
            :: [sldAppendCells
                  (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                    [SldCell.generatorEpsilon])
                  (sldWireLayerOfArity 1)]) := by
        refine SldAreConvertibleLayers.underLayerPrefix (vectorLengthPred + 2)
          (sldAppendCells (sldWireLayerOfArity vectorLengthPred) [SldCell.crossing]) ?_
        rw [crossingPrefixTarget]
        exact paddedRecursion
      have paddedEpsilonLayerEq :
          sldAppendCells
              (sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                [SldCell.generatorEpsilon])
              (sldWireLayerOfArity 1)
            = sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                [SldCell.generatorEpsilon, SldCell.wire] :=
        sldAppendCellsAssoc (sldWireLayerOfArity vectorLengthPred) [SldCell.generatorEpsilon]
          (sldWireLayerOfArity 1)
      have finalLayerEq :
          sldAppendCells (sldWireLayerOfArity vectorLengthPred)
              [SldCell.wire, SldCell.generatorEpsilon]
            = sldAppendCells (sldWireLayerOfArity (vectorLengthPred + 1))
                [SldCell.generatorEpsilon] := by
        show sldAppendCells (sldWireLayerOfArity vectorLengthPred)
            (sldAppendCells (sldWireLayerOfArity 1) [SldCell.generatorEpsilon])
          = sldAppendCells (sldWireLayerOfArity (vectorLengthPred + 1))
              [SldCell.generatorEpsilon]
        rw [(sldAppendCellsAssoc (sldWireLayerOfArity vectorLengthPred)
            (sldWireLayerOfArity 1) [SldCell.generatorEpsilon]).symm,
          sldWireLayerSplitsAtCount]
      have discardPastSwapFires : SldAreConvertibleLayers (vectorLengthPred + 2)
          (sldAppendCells (sldWireLayerOfArity vectorLengthPred) [SldCell.crossing]
            :: [sldAppendCells (sldWireLayerOfArity vectorLengthPred)
                [SldCell.generatorEpsilon, SldCell.wire]])
          [sldAppendCells (sldWireLayerOfArity vectorLengthPred)
            [SldCell.wire, SldCell.generatorEpsilon]] :=
        SldAreConvertibleLayers.fromDiscardPastSwapRow vectorLengthPred 0 []
      rw [paddedEpsilonLayerEq] at recursionUnderCrossing
      rw [finalLayerEq] at discardPastSwapFires
      exact SldAreConvertibleLayers.fromTransitivity gadgetZeroWithSuffix
        (SldAreConvertibleLayers.fromTransitivity recursionUnderCrossing discardPastSwapFires)

/-! ## The bottom-core matrix patches: what multiplying by a deep-cell layer does -/

/-- Multiplying by the deep-eta layer `wires(p) | eta` reads the matrix prefix at columns
below `p` (the eta contributes no source column; its target row multiplies a zero block). -/
theorem lstProductThroughBottomEtaPad (padAboveCount : Nat) (entries : MatrixEntries)
    (rowIndex colIndex : Nat) (isColInside : colIndex < padAboveCount) :
    composeEntries (padAboveCount + 1) entries
        (sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEta]))
        rowIndex colIndex
      = entries rowIndex colIndex := by
  show sumBelow (fun middleIndex => entries rowIndex middleIndex
      * sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEta])
          middleIndex colIndex)
      (padAboveCount + 1)
    = entries rowIndex colIndex
  rw [sumBelowSplitsAtBlock]
  have tailVanishes : sumBelow (fun offsetIndex =>
      entries rowIndex (padAboveCount + offsetIndex)
      * sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEta])
          (padAboveCount + offsetIndex) colIndex) 1 = 0 :=
    sumBelowOfAllZeroIsZero _ 1 (fun offsetIndex _ => by
      have blockForm := sldAppendCellsEntriesAsBlocks (sldWireLayerOfArity padAboveCount)
        [SldCell.generatorEta] (padAboveCount + offsetIndex) colIndex
      rw [sldWireLayerTargetArity, sldWireLayerSourceArity,
        directSumEntryInBottomLeftBlock _ _ offsetIndex isColInside] at blockForm
      rw [blockForm]
      exact rfl)
  rw [tailVanishes, Nat.add_zero]
  refine Eq.trans (sumBelowRespectsPointwise _
    (fun middleIndex => entries rowIndex middleIndex * identityEntries middleIndex colIndex)
    padAboveCount
    (fun middleIndex isMiddleInside => by
      have blockForm := sldAppendCellsEntriesAsBlocks (sldWireLayerOfArity padAboveCount)
        [SldCell.generatorEta] middleIndex colIndex
      rw [sldWireLayerTargetArity, sldWireLayerSourceArity,
        directSumEntryInTopBlock _ _ isMiddleInside isColInside] at blockForm
      rw [blockForm, sldWireLayerEntriesAsIdentity padAboveCount middleIndex colIndex])) ?_
  exact sldProductWithIdentityBeforeCollapses padAboveCount entries rowIndex colIndex
    isColInside

/-- Multiplying by the deep-epsilon layer `wires(p) | epsilon` reads the matrix prefix at
columns below `p`. -/
theorem lstProductThroughBottomEpsilonPad (padAboveCount : Nat) (entries : MatrixEntries)
    (rowIndex colIndex : Nat) (isColInside : colIndex < padAboveCount) :
    composeEntries padAboveCount entries
        (sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEpsilon]))
        rowIndex colIndex
      = entries rowIndex colIndex := by
  refine Eq.trans (sumBelowRespectsPointwise _
    (fun middleIndex => entries rowIndex middleIndex * identityEntries middleIndex colIndex)
    padAboveCount
    (fun middleIndex isMiddleInside => by
      have blockForm := sldAppendCellsEntriesAsBlocks (sldWireLayerOfArity padAboveCount)
        [SldCell.generatorEpsilon] middleIndex colIndex
      rw [sldWireLayerTargetArity, sldWireLayerSourceArity,
        directSumEntryInTopBlock _ _ isMiddleInside isColInside] at blockForm
      rw [blockForm, sldWireLayerEntriesAsIdentity padAboveCount middleIndex colIndex])) ?_
  exact sldProductWithIdentityBeforeCollapses padAboveCount entries rowIndex colIndex
    isColInside

/-- Multiplying by the deep-epsilon layer at the FRESH last column gives zero (the discarded
strand feeds nothing). -/
theorem lstProductThroughBottomEpsilonPadLastColumn (padAboveCount : Nat)
    (entries : MatrixEntries) (rowIndex : Nat) :
    composeEntries padAboveCount entries
        (sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEpsilon]))
        rowIndex padAboveCount
      = 0 :=
  sumBelowOfAllZeroIsZero _ padAboveCount (fun middleIndex isMiddleInside => by
    have blockForm := sldAppendCellsEntriesAsBlocks (sldWireLayerOfArity padAboveCount)
      [SldCell.generatorEpsilon] middleIndex (padAboveCount + 0)
    rw [sldWireLayerTargetArity, sldWireLayerSourceArity,
      directSumEntryInTopRightBlock _ _ 0 isMiddleInside] at blockForm
    have plainForm : sldLayerEntries
        (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEpsilon])
        middleIndex padAboveCount = 0 := blockForm
    rw [plainForm]
    exact rfl)

/-! ## The three CLOSED bottom cores (q = 0): wire, eta, epsilon -/

/-- ETA BOTTOM CORE, geometric form: a deep eta prepended to the canonical list of the
one-wider matrix converts to the canonical list of the plain matrix — slide past the
canonical block, then the fresh zero annihilates the newest fan. -/
theorem lstEtaCellAbsorbsAtBottomPlain (padAboveCount targetArity : Nat)
    (entries : MatrixEntries) :
    SldAreConvertibleLayers padAboveCount
      (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEta]
        :: lstCanonicalLayerList (padAboveCount + 1) targetArity entries)
      (lstCanonicalLayerList padAboveCount targetArity entries) := by
  rw [lstCanonicalSuccUnfolds padAboveCount targetArity entries]
  have etaSlides : SldAreConvertibleLayers padAboveCount
      (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEta]
        :: sldAppendLayers
            (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
            (lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount)))
      (sldAppendLayers
        (sldPadLayersBelow 0 (lstCanonicalLayerList padAboveCount targetArity entries))
        (sldAppendCells
            (sldWireLayerOfArity
              (sldLayersTargetArityFrom padAboveCount
                (lstCanonicalLayerList padAboveCount targetArity entries)))
            [SldCell.generatorEta]
          :: lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount))) :=
    sldLowerLayerSlidesDownPastBlock [SldCell.generatorEta]
      (lstCanonicalLayerList padAboveCount targetArity entries) padAboveCount
      (lstCanonicalLayersAreComposable padAboveCount targetArity entries)
      (lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount))
  rw [sldPadLayersBelowWithZeroIsSelf, lstCanonicalLayersReach] at etaSlides
  have zeroDiesUnderCanon : SldAreConvertibleLayers padAboveCount
      (sldAppendLayers (lstCanonicalLayerList padAboveCount targetArity entries)
        (sldAppendCells (sldWireLayerOfArity targetArity) [SldCell.generatorEta]
          :: lstFanLayerList targetArity (fun mergeRow => entries mergeRow padAboveCount)))
      (sldAppendLayers (lstCanonicalLayerList padAboveCount targetArity entries) []) := by
    refine sldConvUnderPrefixList (lstCanonicalLayerList padAboveCount targetArity entries)
      padAboveCount _ _ ?_
    rw [lstCanonicalLayersReach]
    exact lstFreshZeroAnnihilatesFan targetArity (fun mergeRow => entries mergeRow padAboveCount)
  rw [sldAppendLayersNilRightIsSelf] at zeroDiesUnderCanon
  exact SldAreConvertibleLayers.fromTransitivity etaSlides zeroDiesUnderCanon

/-- ETA BOTTOM CORE, aligned form: the target is the honest product matrix
`M * (wires(p) | eta)` — the geometric form patched by rectangle extensionality. -/
theorem lstEtaCellAbsorbsAtBottom (padAboveCount targetArity : Nat) (entries : MatrixEntries) :
    SldAreConvertibleLayers padAboveCount
      (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEta]
        :: lstCanonicalLayerList (padAboveCount + 1) targetArity entries)
      (lstCanonicalLayerList padAboveCount targetArity
        (composeEntries (padAboveCount + 1) entries
          (sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEta])))) := by
  have matrixPatch : lstCanonicalLayerList padAboveCount targetArity entries
      = lstCanonicalLayerList padAboveCount targetArity
          (composeEntries (padAboveCount + 1) entries
            (sldLayerEntries
              (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEta]))) :=
    lstCanonicalRespectsRectangleAgreement padAboveCount targetArity _ _
      (fun rowIndex colIndex _ isColInside =>
        (lstProductThroughBottomEtaPad padAboveCount entries rowIndex colIndex
          isColInside).symm)
  have plainForm := lstEtaCellAbsorbsAtBottomPlain padAboveCount targetArity entries
  rw [matrixPatch] at plainForm
  exact plainForm

/-- EPSILON BOTTOM CORE, aligned form: a deep epsilon prepended to the canonical list
converts to the canonical list of `M * (wires(p) | epsilon)` (the matrix with a fresh ZERO
column) — slide past the canonical block, then the padded discard IS the zero-column fan. -/
theorem lstEpsilonCellAbsorbsAtBottom (padAboveCount targetArity : Nat)
    (entries : MatrixEntries) :
    SldAreConvertibleLayers (padAboveCount + 1)
      (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEpsilon]
        :: lstCanonicalLayerList padAboveCount targetArity entries)
      (lstCanonicalLayerList (padAboveCount + 1) targetArity
        (composeEntries padAboveCount entries
          (sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount)
              [SldCell.generatorEpsilon])))) := by
  have epsilonSlides : SldAreConvertibleLayers (padAboveCount + 1)
      (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEpsilon]
        :: sldAppendLayers
            (sldPadLayersBelow 0 (lstCanonicalLayerList padAboveCount targetArity entries)) [])
      (sldAppendLayers
        (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
        (sldAppendCells
            (sldWireLayerOfArity
              (sldLayersTargetArityFrom padAboveCount
                (lstCanonicalLayerList padAboveCount targetArity entries)))
            [SldCell.generatorEpsilon]
          :: [])) :=
    sldLowerLayerSlidesDownPastBlock [SldCell.generatorEpsilon]
      (lstCanonicalLayerList padAboveCount targetArity entries) padAboveCount
      (lstCanonicalLayersAreComposable padAboveCount targetArity entries) []
  rw [sldPadLayersBelowWithZeroIsSelf, sldAppendLayersNilRightIsSelf,
    lstCanonicalLayersReach] at epsilonSlides
  have paddedReach : sldLayersTargetArityFrom (padAboveCount + 1)
      (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
      = targetArity + 1 := by
    have liftedReach := sldPadLayersBelowTargetArityFrom 1
      (lstCanonicalLayerList padAboveCount targetArity entries) padAboveCount
    rw [lstCanonicalLayersReach] at liftedReach
    exact liftedReach
  have discardBecomesZeroFan : SldAreConvertibleLayers (padAboveCount + 1)
      (sldAppendLayers
        (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
        [sldAppendCells (sldWireLayerOfArity targetArity) [SldCell.generatorEpsilon]])
      (sldAppendLayers
        (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
        (lstFanLayerList targetArity (fun _sourceRow => 0))) := by
    refine sldConvUnderPrefixList
      (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
      (padAboveCount + 1) _ _ ?_
    rw [paddedReach]
    exact SldAreConvertibleLayers.fromSymmetry (lstZeroColumnFanIsDiscard targetArity)
  have refold : lstCanonicalLayerList (padAboveCount + 1) targetArity
      (composeEntries padAboveCount entries
        (sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEpsilon])))
      = sldAppendLayers
          (sldPadLayersBelow 1 (lstCanonicalLayerList padAboveCount targetArity entries))
          (lstFanLayerList targetArity (fun _sourceRow => 0)) := by
    rw [lstCanonicalSuccUnfolds padAboveCount targetArity
        (composeEntries padAboveCount entries
          (sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEpsilon]))),
      lstCanonicalRespectsRectangleAgreement padAboveCount targetArity
        (composeEntries padAboveCount entries
          (sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.generatorEpsilon])))
        entries
        (fun rowIndex colIndex _ isColInside =>
          lstProductThroughBottomEpsilonPad padAboveCount entries rowIndex colIndex
            isColInside),
      lstFanRespectsColumnAgreement targetArity
        (fun mergeRow =>
          composeEntries padAboveCount entries
            (sldLayerEntries
              (sldAppendCells (sldWireLayerOfArity padAboveCount)
                [SldCell.generatorEpsilon]))
            mergeRow padAboveCount)
        (fun _sourceRow => 0)
        (fun mergeRow _ =>
          lstProductThroughBottomEpsilonPadLastColumn padAboveCount entries mergeRow)]
  rw [refold]
  exact SldAreConvertibleLayers.fromTransitivity epsilonSlides discardBecomesZeroFan

/-- WIRE BOTTOM CORE, aligned form: the all-wire padded layer deletes and the matrix is
unchanged (the wire layer is the identity). -/
theorem lstWireCellAbsorbsAtBottom (padAboveCount targetArity : Nat) (entries : MatrixEntries) :
    SldAreConvertibleLayers (padAboveCount + 1)
      (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.wire]
        :: lstCanonicalLayerList (padAboveCount + 1) targetArity entries)
      (lstCanonicalLayerList (padAboveCount + 1) targetArity
        (composeEntries (padAboveCount + 1) entries
          (sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.wire])))) := by
  have padIsWires : sldAppendCells (sldWireLayerOfArity padAboveCount) [SldCell.wire]
      = sldWireLayerOfArity (padAboveCount + 1) :=
    sldWireLayerSplitsAtCount padAboveCount 1
  rw [padIsWires]
  have matrixPatch : lstCanonicalLayerList (padAboveCount + 1) targetArity
      (composeEntries (padAboveCount + 1) entries
        (sldLayerEntries (sldWireLayerOfArity (padAboveCount + 1))))
      = lstCanonicalLayerList (padAboveCount + 1) targetArity entries :=
    lstCanonicalRespectsRectangleAgreement (padAboveCount + 1) targetArity _ _
      (fun rowIndex colIndex _ isColInside =>
        lstProductThroughWireLayerCollapses (padAboveCount + 1) entries rowIndex colIndex
          isColInside)
  rw [matrixPatch]
  exact lstWireLayerBeforeChainDeletes (padAboveCount + 1)
    (lstCanonicalLayerList (padAboveCount + 1) targetArity entries)
    (lstCanonicalLayersAreComposable (padAboveCount + 1) targetArity entries)

/-! ## THE BELOW-PAD REDUCTION: absorption at any below pad reduces to pad zero -/

/-- Absorption of a padded cell at ANY below-pad count follows from absorption at pad zero —
the induction rides the canonical builder's column recursion: the outermost below-pad wire
peels into the padded-canonical prefix (one column of the matrix passes through untouched),
the two restriction lemmas discharge the matrix bookkeeping, and the fan of the passed
column refolds by the succ unfold.  Generic across all six cell kinds. -/
theorem lstCellAbsorptionLiftsThroughBelowPads (absorbedCell : SldCell)
    (padAboveCount targetArity : Nat) (entries : MatrixEntries)
    (absorbsAtBottom : SldAreConvertibleLayers
      (padAboveCount + sldLayerSourceArity [absorbedCell])
      (sldPadLayer padAboveCount 0 [absorbedCell]
        :: lstCanonicalLayerList (padAboveCount + sldLayerTargetArity [absorbedCell])
            targetArity entries)
      (lstCanonicalLayerList (padAboveCount + sldLayerSourceArity [absorbedCell]) targetArity
        (composeEntries (padAboveCount + sldLayerTargetArity [absorbedCell]) entries
          (sldLayerEntries (sldPadLayer padAboveCount 0 [absorbedCell]))))) :
    (padBelowCount : Nat) ->
    SldAreConvertibleLayers
      (padAboveCount + (sldLayerSourceArity [absorbedCell] + padBelowCount))
      (sldPadLayer padAboveCount padBelowCount [absorbedCell]
        :: lstCanonicalLayerList
            (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowCount)) targetArity
            entries)
      (lstCanonicalLayerList
        (padAboveCount + (sldLayerSourceArity [absorbedCell] + padBelowCount)) targetArity
        (composeEntries
          (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowCount)) entries
          (sldLayerEntries (sldPadLayer padAboveCount padBelowCount [absorbedCell]))))
  | 0 => absorbsAtBottom
  | padBelowPred + 1 => by
      show SldAreConvertibleLayers
        (padAboveCount + (sldLayerSourceArity [absorbedCell] + padBelowPred) + 1)
        (sldPadLayer padAboveCount (padBelowPred + 1) [absorbedCell]
          :: lstCanonicalLayerList
              (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred) + 1)
              targetArity entries)
        (lstCanonicalLayerList
          (padAboveCount + (sldLayerSourceArity [absorbedCell] + padBelowPred) + 1) targetArity
          (composeEntries
            (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred) + 1) entries
            (sldLayerEntries (sldPadLayer padAboveCount (padBelowPred + 1) [absorbedCell]))))
      rw [(sldPadLayerBelowExtension padAboveCount padBelowPred 1 [absorbedCell]).symm,
        lstCanonicalSuccUnfolds
          (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred)) targetArity
          entries]
      have agreementPrefix : ∀ rowIndex colIndex, rowIndex < targetArity ->
          colIndex < padAboveCount + (sldLayerSourceArity [absorbedCell] + padBelowPred) ->
          composeEntries
            (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred) + 1) entries
            (sldLayerEntries
              (sldAppendCells (sldPadLayer padAboveCount padBelowPred [absorbedCell])
                (sldWireLayerOfArity 1))) rowIndex colIndex
          = composeEntries
              (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred)) entries
              (sldLayerEntries (sldPadLayer padAboveCount padBelowPred [absorbedCell]))
              rowIndex colIndex := by
        intro rowIndex colIndex _ isColInside
        have restricted := lstProductAgainstAppendedLayerRestricts
          (sldPadLayer padAboveCount padBelowPred [absorbedCell]) (sldWireLayerOfArity 1)
          entries rowIndex colIndex
          (by
            rw [sldPadLayerSourceArity]
            exact isColInside)
        rw [sldPadLayerTargetArity, sldWireLayerTargetArity] at restricted
        exact restricted
      have agreementLastColumn : ∀ mergeRow, mergeRow < targetArity ->
          composeEntries
            (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred) + 1) entries
            (sldLayerEntries
              (sldAppendCells (sldPadLayer padAboveCount padBelowPred [absorbedCell])
                (sldWireLayerOfArity 1))) mergeRow
            (padAboveCount + (sldLayerSourceArity [absorbedCell] + padBelowPred))
          = entries mergeRow
              (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred)) := by
        intro mergeRow _
        have lastColumn := lstProductLastColumnThroughBelowWirePad
          (sldPadLayer padAboveCount padBelowPred [absorbedCell]) entries mergeRow
        rw [sldPadLayerTargetArity, sldPadLayerSourceArity] at lastColumn
        exact lastColumn
      have refold : lstCanonicalLayerList
          (padAboveCount + (sldLayerSourceArity [absorbedCell] + padBelowPred) + 1) targetArity
          (composeEntries
            (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred) + 1) entries
            (sldLayerEntries
              (sldAppendCells (sldPadLayer padAboveCount padBelowPred [absorbedCell])
                (sldWireLayerOfArity 1))))
          = sldAppendLayers
              (sldPadLayersBelow 1
                (lstCanonicalLayerList
                  (padAboveCount + (sldLayerSourceArity [absorbedCell] + padBelowPred))
                  targetArity
                  (composeEntries
                    (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred))
                    entries
                    (sldLayerEntries
                      (sldPadLayer padAboveCount padBelowPred [absorbedCell])))))
              (lstFanLayerList targetArity
                (fun mergeRow => entries mergeRow
                  (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred)))) := by
        rw [lstCanonicalSuccUnfolds
            (padAboveCount + (sldLayerSourceArity [absorbedCell] + padBelowPred)) targetArity
            (composeEntries
              (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred) + 1)
              entries
              (sldLayerEntries
                (sldAppendCells (sldPadLayer padAboveCount padBelowPred [absorbedCell])
                  (sldWireLayerOfArity 1)))),
          lstCanonicalRespectsRectangleAgreement
            (padAboveCount + (sldLayerSourceArity [absorbedCell] + padBelowPred)) targetArity
            _ _ agreementPrefix,
          lstFanRespectsColumnAgreement targetArity
            (fun mergeRow =>
              composeEntries
                (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred) + 1)
                entries
                (sldLayerEntries
                  (sldAppendCells (sldPadLayer padAboveCount padBelowPred [absorbedCell])
                    (sldWireLayerOfArity 1))) mergeRow
                (padAboveCount + (sldLayerSourceArity [absorbedCell] + padBelowPred)))
            (fun mergeRow => entries mergeRow
              (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred)))
            agreementLastColumn]
      rw [refold]
      have paddedRecursion : SldAreConvertibleLayers
          (padAboveCount + (sldLayerSourceArity [absorbedCell] + padBelowPred) + 1)
          (sldPadLayersBelow 1
            (sldPadLayer padAboveCount padBelowPred [absorbedCell]
              :: lstCanonicalLayerList
                  (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred))
                  targetArity entries))
          (sldPadLayersBelow 1
            (lstCanonicalLayerList
              (padAboveCount + (sldLayerSourceArity [absorbedCell] + padBelowPred))
              targetArity
              (composeEntries
                (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred)) entries
                (sldLayerEntries (sldPadLayer padAboveCount padBelowPred [absorbedCell]))))) :=
        sldConvPadsBelow
          (lstCellAbsorptionLiftsThroughBelowPads absorbedCell padAboveCount targetArity
            entries absorbsAtBottom padBelowPred) 1
      exact sldConvAppendsSuffix paddedRecursion
        (lstFanLayerList targetArity
          (fun mergeRow => entries mergeRow
            (padAboveCount + (sldLayerTargetArity [absorbedCell] + padBelowPred))))

/-! ## The CLOSED absorption theorems at ALL pads: wire, eta, epsilon -/

/-- WIRE ABSORPTION at all pads: the all-wire padded layer deletes; the matrix target is the
honest product with the padded-layer entries. -/
theorem lstWireCellAbsorbs (padAboveCount padBelowCount targetArity : Nat)
    (entries : MatrixEntries) :
    SldAreConvertibleLayers (padAboveCount + (1 + padBelowCount))
      (sldPadLayer padAboveCount padBelowCount [SldCell.wire]
        :: lstCanonicalLayerList (padAboveCount + (1 + padBelowCount)) targetArity entries)
      (lstCanonicalLayerList (padAboveCount + (1 + padBelowCount)) targetArity
        (composeEntries (padAboveCount + (1 + padBelowCount)) entries
          (sldLayerEntries (sldPadLayer padAboveCount padBelowCount [SldCell.wire])))) :=
  lstCellAbsorptionLiftsThroughBelowPads SldCell.wire padAboveCount targetArity entries
    (lstWireCellAbsorbsAtBottom padAboveCount targetArity entries) padBelowCount

/-- ETA ABSORPTION at all pads: a padded fresh zero is absorbed, deleting its column of the
canonical form; the matrix target is the honest product with the padded-layer entries. -/
theorem lstEtaCellAbsorbs (padAboveCount padBelowCount targetArity : Nat)
    (entries : MatrixEntries) :
    SldAreConvertibleLayers (padAboveCount + (0 + padBelowCount))
      (sldPadLayer padAboveCount padBelowCount [SldCell.generatorEta]
        :: lstCanonicalLayerList (padAboveCount + (1 + padBelowCount)) targetArity entries)
      (lstCanonicalLayerList (padAboveCount + (0 + padBelowCount)) targetArity
        (composeEntries (padAboveCount + (1 + padBelowCount)) entries
          (sldLayerEntries (sldPadLayer padAboveCount padBelowCount [SldCell.generatorEta])))) :=
  lstCellAbsorptionLiftsThroughBelowPads SldCell.generatorEta padAboveCount targetArity entries
    (lstEtaCellAbsorbsAtBottom padAboveCount targetArity entries) padBelowCount

/-- EPSILON ABSORPTION at all pads: a padded discard is absorbed, inserting a zero column
into the canonical form; the matrix target is the honest product with the padded-layer
entries. -/
theorem lstEpsilonCellAbsorbs (padAboveCount padBelowCount targetArity : Nat)
    (entries : MatrixEntries) :
    SldAreConvertibleLayers (padAboveCount + (1 + padBelowCount))
      (sldPadLayer padAboveCount padBelowCount [SldCell.generatorEpsilon]
        :: lstCanonicalLayerList (padAboveCount + (0 + padBelowCount)) targetArity entries)
      (lstCanonicalLayerList (padAboveCount + (1 + padBelowCount)) targetArity
        (composeEntries (padAboveCount + (0 + padBelowCount)) entries
          (sldLayerEntries
            (sldPadLayer padAboveCount padBelowCount [SldCell.generatorEpsilon])))) :=
  lstCellAbsorptionLiftsThroughBelowPads SldCell.generatorEpsilon padAboveCount targetArity
    entries (lstEpsilonCellAbsorbsAtBottom padAboveCount targetArity entries) padBelowCount

/-! ## The three OPEN bottom cores (mu, delta, crossing) — named, owners false

Each remaining absorption reduces (by the slide past the canonical block, exactly as in the
closed cores, plus the below-pad reduction) to ONE fan-level interaction statement.  The
statements are recorded here as the honest remaining bill; none is walled — no core has
eaten three genuinely-different failed attacks yet.

* MU = FAN DUPLICATION `(x + y) merged once = x merged, then y merged`: reduces further to a
  GADGET-MU lemma `(wire | mu) ; gadget(s) ~ (gadget(s) | wire) ; (wire | gadget(s)) ;
  (mu | wire)` (needs a SCALE-MU distributivity induction `mu ; scale(s) ~
  (scale(s) | scale(s)) ; mu` riding B1 + M1/M4 + Nmu), then the same
  padsAbove/blockSlide/padsBelow assembly as the eta core — the fan appears TWICE on the
  right, duplicated by the recursion.
* DELTA = FAN FUSION `copied source merged with A then B = merged once with A + B`: reduces
  to a GADGET-DELTA lemma `(wire | delta) ; (gadget(a) | wire) ; (wire | gadget(b)) ~
  gadget(a + b) ; (delta | wire)` (needs a SCALE-FUSION induction `delta ; (scale(a) |
  scale(b)) ; mu ~ scale(a + b)`, which in turn wants the crossing's block naturality for
  the mirror unfold), then the mu-core assembly run backwards.
* CROSSING = TWO-FAN SWAP: the commission's predicted sticking point — the two adjacent
  column fans commute after a source swap; the gadget rungs OVERLAP on the climbing source
  strand, so no disjoint-slide argument applies and a genuine Coxeter-style double induction
  over both fans is required. -/

/-- OPEN (mu bottom core): the fan duplicates an added source —
`(wires(t) | mu) ; fan(t, col) ~ (fan(t, col) | wire) ; fan(t, col)`. -/
def lstMuFanDuplicationStatement : Prop :=
  ∀ (vectorLength : Nat) (columnEntries : Nat -> Nat),
    SldAreConvertibleLayers (vectorLength + 2)
      (sldAppendCells (sldWireLayerOfArity vectorLength) [SldCell.generatorMu]
        :: lstFanLayerList vectorLength columnEntries)
      (sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList vectorLength columnEntries))
        (lstFanLayerList vectorLength columnEntries))

/-- OPEN (delta bottom core): two fans over one copied source fuse into the sum-column fan —
`(wires(t) | delta) ; (fan(t, A) | wire) ; fan(t, B) ~ fan(t, A + B)`. -/
def lstDeltaFanFusionStatement : Prop :=
  ∀ (vectorLength : Nat) (firstColumn secondColumn : Nat -> Nat),
    SldAreConvertibleLayers (vectorLength + 1)
      (sldAppendCells (sldWireLayerOfArity vectorLength) [SldCell.generatorDelta]
        :: sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList vectorLength firstColumn))
            (lstFanLayerList vectorLength secondColumn))
      (lstFanLayerList vectorLength
        (fun mergeRow => firstColumn mergeRow + secondColumn mergeRow))

/-- OPEN (crossing bottom core): two adjacent fans swap when their sources swap —
`(wires(t) | tau) ; (fan(t, A) | wire) ; fan(t, B) ~ (fan(t, B) | wire) ; fan(t, A)`. -/
def lstCrossingTwoFanSwapStatement : Prop :=
  ∀ (vectorLength : Nat) (firstColumn secondColumn : Nat -> Nat),
    SldAreConvertibleLayers (vectorLength + 2)
      (sldAppendCells (sldWireLayerOfArity vectorLength) [SldCell.crossing]
        :: sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList vectorLength firstColumn))
            (lstFanLayerList vectorLength secondColumn))
      (sldAppendLayers (sldPadLayersBelow 1 (lstFanLayerList vectorLength secondColumn))
        (lstFanLayerList vectorLength firstColumn))

/-- OPEN (the full staircase): every composable strict-layer diagram converts to the
canonical layer list of its own denotation.  Waits on the three open cores plus the
layer/list assembly. -/
def lstCanonicalReductionOverStrictLayersStatement : Prop :=
  ∀ (diagram : SldDiagram), sldIsComposable diagram = true ->
    SldAreConvertibleLayers diagram.sourceArity diagram.layers
      (lstCanonicalLayerList diagram.sourceArity (sldTargetArity diagram) (sldDenote diagram))

/-- Owner (false): the mu fan-duplication core is NOT proven in this round. -/
def lstMuFanDuplicationProved : Bool := false

/-- Owner (false): the delta fan-fusion core is NOT proven in this round. -/
def lstDeltaFanFusionProved : Bool := false

/-- Owner (false): the crossing two-fan-swap core is NOT proven in this round. -/
def lstCrossingTwoFanSwapProved : Bool := false

/-- Owner (false): the full canonical reduction over strict layers is NOT proven in this
round; `fxLafontStrictLayer_hasCanonicalCompleteness` (StrictLayerEmbedding) stays false. -/
def lstCanonicalReductionOverStrictLayersProved : Bool := false

/-- Stage-2 marker (true): the wire/eta/epsilon third of the absorption ladder is CLOSED at
all pads against the honest product-matrix targets, on top of the generic below-pad
reduction. -/
def fxLafontStaircase_hasWireEtaEpsilonAbsorption : Bool := true

end FX1Poly.Polygraph.Omega.LafontProp
