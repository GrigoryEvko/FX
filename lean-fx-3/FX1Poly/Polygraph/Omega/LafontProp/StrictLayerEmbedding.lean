import FX1Poly.Polygraph.Omega.LafontProp.StrictLayerDiagram
import FX1Poly.Polygraph.Omega.LafontProp.CanonicalReduction

/-! # Polygraph/Omega/LafontProp/StrictLayerEmbedding — the congruence, its soundness, and the
embedding of the binary syntax (LAFONT-REPAIR stage 1, bricks C+D+E)

Stage-1 file 2, on top of the `StrictLayerDiagram` carrier:

* THE CONGRUENCE (`SldAreConvertibleLayers`) — a BOUNDARY-INDEXED relation on layer lists:
  groupoid closure, congruence under a leading layer (free outer index), the TWO LAYER-SPLIT
  moves (a layer `X ++ Y` splits into `(X | wires) ; (wires | Y)` in either order — the
  interchange/exchange of [DelpeuchVicary2018], from which the disjoint-cell exchange is
  DERIVED, `sldDisjointLayersExchange`), and the 18 relation rows of the r1 presentation as
  LOCAL WINDOW REWRITES through the single combinator `sldPadWindow` (wires above/below, any
  suffix).  In this carrier the (co)unit and involution rows have the EMPTY LIST as right
  window — identity layers literally vanish, which is exactly what the r3 padding refutation
  demanded and the binary syntax could not express.
* PER-ROW COHERENCE GATE (`sldAllEighteenRowWindowsCohere`, kernel `rfl`): each window pair is
  composable, boundary-exact, and Mat(N)-sound.
* SOUNDNESS (`sldConvertibleLayersDenoteEqualEntries`): convertible layer lists have EQUAL
  denotations at every column inside the source boundary (any row) — a single induction over
  the congruence, the row cases through the pad-sandwich lemmas, the split cases through the
  block-recombination lemmas.  Bool form + the NEGATIVE decision direction
  (`sldNotConvertibleOfDistinctDenotes`).
* DEFENSIVE FIRES (stage D, file-2 half): the r30 refuted unit pair `(id1 | eta) ; mu ~ id1`
  is `[[wire, eta], [mu]] ~ []` — ONE row instance (fire 2a); the associativity pair likewise
  (fire 2b).  THE EX-SEPARATOR: `sldOfWireDiagram` maps the r3 separator `id0 | delta` and
  bare `delta` to the SAME `SldDiagram` by kernel `rfl`
  (`sldEmbeddingDissolvesTheSeparator`) — the anomaly-parity invariant that refuted the old
  completeness sees one term where it saw two (`sldEmbeddingCollapsesAnomalyParity`).
* THE EMBEDDING (stage E): `sldOfWireDiagram : WireDiagram m n -> SldDiagram` — identities to
  the empty list, composition to append, tensor to the zip, generators to one-cell layers.
  Shipped with source/target-arity agreement, composability
  (`sldOfWireDiagramIsComposable`), and THE BRIDGE: denotation agreement on the full
  rectangle (`sldOfWireDiagramDenoteAgrees` — the layer semantics restricts to the r1 matrix
  semantics along the embedding).
* CONVERTIBILITY TRANSPORT (stage E, hard half): see the marker section at the end of the
  file for the machine-checked status of `AreConvertibleDiagrams d e ->
  SldAreConvertibleLayers _ (embed d) (embed e)`.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; audit twin with per-decl
`#assert_no_axioms` plus an independent `#print axioms` probe. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.LafontProp

/-! ## Pad-window semantics: the sandwich form and the pad congruence -/

/-- A padded layer denotes the identity-window-identity sandwich (pointwise, everywhere). -/
theorem sldPadLayerEntriesAsSandwich (padAboveCount padBelowCount : Nat)
    (windowLayer : SldLayer) (rowIndex colIndex : Nat) :
    sldLayerEntries (sldPadLayer padAboveCount padBelowCount windowLayer) rowIndex colIndex
      = directSumEntries padAboveCount padAboveCount identityEntries
          (directSumEntries (sldLayerTargetArity windowLayer) (sldLayerSourceArity windowLayer)
            (sldLayerEntries windowLayer) identityEntries) rowIndex colIndex := by
  refine Eq.trans (sldAppendCellsEntriesAsBlocks (sldWireLayerOfArity padAboveCount)
    (sldAppendCells windowLayer (sldWireLayerOfArity padBelowCount)) rowIndex colIndex) ?_
  rw [sldWireLayerTargetArity, sldWireLayerSourceArity]
  refine sldDirectSumRespectsEntryAgreement padAboveCount padAboveCount
    (sldLayerEntries (sldWireLayerOfArity padAboveCount)) identityEntries
    (sldLayerEntries (sldAppendCells windowLayer (sldWireLayerOfArity padBelowCount)))
    (directSumEntries (sldLayerTargetArity windowLayer) (sldLayerSourceArity windowLayer)
      (sldLayerEntries windowLayer) identityEntries)
    rowIndex colIndex
    (fun _ _ => sldWireLayerEntriesAsIdentity padAboveCount rowIndex colIndex) ?_
  intro rowOffset colOffset _ _
  refine Eq.trans (sldAppendCellsEntriesAsBlocks windowLayer
    (sldWireLayerOfArity padBelowCount) rowOffset colOffset) ?_
  exact sldDirectSumRespectsEntryAgreement (sldLayerTargetArity windowLayer)
    (sldLayerSourceArity windowLayer)
    (sldLayerEntries windowLayer) (sldLayerEntries windowLayer)
    (sldLayerEntries (sldWireLayerOfArity padBelowCount)) identityEntries rowOffset colOffset
    (fun _ _ => rfl)
    (fun deepRowOffset deepColOffset _ _ =>
      sldWireLayerEntriesAsIdentity padBelowCount deepRowOffset deepColOffset)

/-- THE SANDWICH LEMMA: a padded window denotes `id_a (+) denote(window) (+) id_b` on the
padded rectangle. -/
theorem sldPadWindowDenoteAsSandwichEntry (padAboveCount padBelowCount : Nat) :
    (windowLayers : List SldLayer) -> (windowBoundary : Nat) ->
    sldLayersAreComposableFrom windowBoundary windowLayers = true ->
    (rowIndex colIndex : Nat) ->
    rowIndex < padAboveCount
      + (sldLayersTargetArityFrom windowBoundary windowLayers + padBelowCount) ->
    colIndex < padAboveCount + (windowBoundary + padBelowCount) ->
    sldLayersDenote (sldPadWindow padAboveCount padBelowCount windowLayers) rowIndex colIndex
      = directSumEntries padAboveCount padAboveCount identityEntries
          (directSumEntries (sldLayersTargetArityFrom windowBoundary windowLayers)
            windowBoundary (sldLayersDenote windowLayers) identityEntries) rowIndex colIndex
  | [], windowBoundary, _, rowIndex, colIndex, _, _ =>
      Eq.trans (sldDirectSumOfIdentitiesEntry padAboveCount rowIndex colIndex).symm
        (sldDirectSumRespectsEntryAgreement padAboveCount padAboveCount
          identityEntries identityEntries identityEntries
          (directSumEntries windowBoundary windowBoundary identityEntries identityEntries)
          rowIndex colIndex (fun _ _ => rfl)
          (fun rowOffset colOffset _ _ =>
            (sldDirectSumOfIdentitiesEntry windowBoundary rowOffset colOffset).symm))
  | headLayer :: tailLayers, windowBoundary, isChainComposable, rowIndex, colIndex,
      isRowInside, isColInside => by
      have doesHeadMatch : sldLayerSourceArity headLayer = windowBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isChainComposable)
      have doesTailCompose := rightIsTrueOfAndTrue isChainComposable
      rw [doesHeadMatch.symm] at isColInside
      rw [doesHeadMatch.symm]
      show composeEntries (sldLayerTargetArity (sldPadLayer padAboveCount padBelowCount headLayer))
          (sldLayersDenote (sldPadWindow padAboveCount padBelowCount tailLayers))
          (sldLayerEntries (sldPadLayer padAboveCount padBelowCount headLayer))
          rowIndex colIndex
        = directSumEntries padAboveCount padAboveCount identityEntries
            (directSumEntries
              (sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers)
              (sldLayerSourceArity headLayer)
              (composeEntries (sldLayerTargetArity headLayer) (sldLayersDenote tailLayers)
                (sldLayerEntries headLayer)) identityEntries) rowIndex colIndex
      rw [sldPadLayerTargetArity]
      refine Eq.trans (sldProductRespectsEntryAgreement
        (padAboveCount + (sldLayerTargetArity headLayer + padBelowCount))
        (sldLayersDenote (sldPadWindow padAboveCount padBelowCount tailLayers))
        (directSumEntries padAboveCount padAboveCount identityEntries
          (directSumEntries
            (sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers)
            (sldLayerTargetArity headLayer) (sldLayersDenote tailLayers) identityEntries))
        (sldLayerEntries (sldPadLayer padAboveCount padBelowCount headLayer))
        (directSumEntries padAboveCount padAboveCount identityEntries
          (directSumEntries (sldLayerTargetArity headLayer) (sldLayerSourceArity headLayer)
            (sldLayerEntries headLayer) identityEntries))
        rowIndex colIndex
        (fun middleIndex isMiddleInside =>
          sldPadWindowDenoteAsSandwichEntry padAboveCount padBelowCount tailLayers
            (sldLayerTargetArity headLayer) doesTailCompose rowIndex middleIndex
            isRowInside isMiddleInside)
        (fun middleIndex _ =>
          sldPadLayerEntriesAsSandwich padAboveCount padBelowCount headLayer
            middleIndex colIndex)) ?_
      refine Eq.trans (sldDirectSumMultiplicativityEntry padAboveCount
        (sldLayerTargetArity headLayer + padBelowCount) padAboveCount padAboveCount
        identityEntries
        (directSumEntries (sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers)
          (sldLayerTargetArity headLayer) (sldLayersDenote tailLayers) identityEntries)
        identityEntries
        (directSumEntries (sldLayerTargetArity headLayer) (sldLayerSourceArity headLayer)
          (sldLayerEntries headLayer) identityEntries)
        rowIndex colIndex) ?_
      refine sldDirectSumRespectsEntryAgreement padAboveCount padAboveCount
        (composeEntries padAboveCount identityEntries identityEntries) identityEntries
        (composeEntries (sldLayerTargetArity headLayer + padBelowCount)
          (directSumEntries
            (sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers)
            (sldLayerTargetArity headLayer) (sldLayersDenote tailLayers) identityEntries)
          (directSumEntries (sldLayerTargetArity headLayer) (sldLayerSourceArity headLayer)
            (sldLayerEntries headLayer) identityEntries))
        (directSumEntries
          (sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers)
          (sldLayerSourceArity headLayer)
          (composeEntries (sldLayerTargetArity headLayer) (sldLayersDenote tailLayers)
            (sldLayerEntries headLayer)) identityEntries)
        rowIndex colIndex
        (fun isRowInPad _ =>
          sldProductWithIdentityAfterCollapses padAboveCount identityEntries rowIndex
            colIndex isRowInPad) ?_
      intro rowOffset colOffset doesRowSplit doesColSplit
      refine Eq.trans (sldDirectSumMultiplicativityEntry (sldLayerTargetArity headLayer)
        padBelowCount
        (sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers)
        (sldLayerSourceArity headLayer)
        (sldLayersDenote tailLayers) identityEntries
        (sldLayerEntries headLayer) identityEntries rowOffset colOffset) ?_
      refine sldDirectSumRespectsEntryAgreement
        (sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers)
        (sldLayerSourceArity headLayer)
        (composeEntries (sldLayerTargetArity headLayer) (sldLayersDenote tailLayers)
          (sldLayerEntries headLayer))
        (composeEntries (sldLayerTargetArity headLayer) (sldLayersDenote tailLayers)
          (sldLayerEntries headLayer))
        (composeEntries padBelowCount identityEntries identityEntries) identityEntries
        rowOffset colOffset (fun _ _ => rfl) ?_
      intro deepRowOffset deepColOffset _ doesDeepColSplit
      refine sldProductWithIdentityBeforeCollapses padBelowCount identityEntries
        deepRowOffset deepColOffset ?_
      rw [doesColSplit] at isColInside
      have isOffsetInside : colOffset < sldLayerSourceArity headLayer + padBelowCount :=
        ltOfAddLtAddLeft padAboveCount isColInside
      rw [doesDeepColSplit] at isOffsetInside
      exact ltOfAddLtAddLeft (sldLayerSourceArity headLayer) isOffsetInside

/-- PAD CONGRUENCE: windows with matching boundaries and agreeing denotations stay agreeing
under any wire pad. -/
theorem sldPaddedWindowsDenoteAgreeEntry (padAboveCount padBelowCount : Nat)
    (leftWindow rightWindow : List SldLayer) (windowSourceArity windowTargetArity : Nat)
    (isLeftComposable : sldLayersAreComposableFrom windowSourceArity leftWindow = true)
    (isRightComposable : sldLayersAreComposableFrom windowSourceArity rightWindow = true)
    (doesLeftReach : sldLayersTargetArityFrom windowSourceArity leftWindow = windowTargetArity)
    (doesRightReach : sldLayersTargetArityFrom windowSourceArity rightWindow = windowTargetArity)
    (doWindowsAgree : ∀ windowRow windowCol, windowRow < windowTargetArity ->
      windowCol < windowSourceArity ->
      sldLayersDenote leftWindow windowRow windowCol
        = sldLayersDenote rightWindow windowRow windowCol)
    (rowIndex colIndex : Nat)
    (isRowInside : rowIndex < padAboveCount + (windowTargetArity + padBelowCount))
    (isColInside : colIndex < padAboveCount + (windowSourceArity + padBelowCount)) :
    sldLayersDenote (sldPadWindow padAboveCount padBelowCount leftWindow) rowIndex colIndex
      = sldLayersDenote (sldPadWindow padAboveCount padBelowCount rightWindow)
          rowIndex colIndex := by
  have isLeftRowInside : rowIndex < padAboveCount
      + (sldLayersTargetArityFrom windowSourceArity leftWindow + padBelowCount) := by
    rw [doesLeftReach]
    exact isRowInside
  have isRightRowInside : rowIndex < padAboveCount
      + (sldLayersTargetArityFrom windowSourceArity rightWindow + padBelowCount) := by
    rw [doesRightReach]
    exact isRowInside
  refine Eq.trans (sldPadWindowDenoteAsSandwichEntry padAboveCount padBelowCount leftWindow
    windowSourceArity isLeftComposable rowIndex colIndex isLeftRowInside isColInside)
    (Eq.trans ?_ (sldPadWindowDenoteAsSandwichEntry padAboveCount padBelowCount rightWindow
      windowSourceArity isRightComposable rowIndex colIndex isRightRowInside isColInside).symm)
  rw [doesLeftReach, doesRightReach]
  refine sldDirectSumRespectsEntryAgreement padAboveCount padAboveCount
    identityEntries identityEntries
    (directSumEntries windowTargetArity windowSourceArity (sldLayersDenote leftWindow)
      identityEntries)
    (directSumEntries windowTargetArity windowSourceArity (sldLayersDenote rightWindow)
      identityEntries)
    rowIndex colIndex (fun _ _ => rfl) ?_
  intro rowOffset colOffset _ _
  exact sldDirectSumRespectsEntryAgreement windowTargetArity windowSourceArity
    (sldLayersDenote leftWindow) (sldLayersDenote rightWindow)
    identityEntries identityEntries rowOffset colOffset
    (fun isRowInWindow isColInWindow => doWindowsAgree rowOffset colOffset isRowInWindow
      isColInWindow)
    (fun _ _ _ _ => rfl)

/-- THE ROW-REWRITE SOUNDNESS ENGINE: replacing a padded window by a boundary-matching,
denotation-agreeing window preserves the denotation of the whole list, any suffix, any pads,
at every column inside the source boundary. -/
theorem sldPaddedRowRewritePreservesDenoteEntry
    (leftWindow rightWindow : List SldLayer) (windowSourceArity windowTargetArity : Nat)
    (isLeftComposable : sldLayersAreComposableFrom windowSourceArity leftWindow = true)
    (isRightComposable : sldLayersAreComposableFrom windowSourceArity rightWindow = true)
    (doesLeftReach : sldLayersTargetArityFrom windowSourceArity leftWindow = windowTargetArity)
    (doesRightReach : sldLayersTargetArityFrom windowSourceArity rightWindow = windowTargetArity)
    (doWindowsAgree : ∀ windowRow windowCol, windowRow < windowTargetArity ->
      windowCol < windowSourceArity ->
      sldLayersDenote leftWindow windowRow windowCol
        = sldLayersDenote rightWindow windowRow windowCol)
    (padAboveCount padBelowCount : Nat) (suffixLayers : List SldLayer)
    (rowIndex colIndex : Nat)
    (isColInside : colIndex < padAboveCount + (windowSourceArity + padBelowCount)) :
    sldLayersDenote
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount leftWindow) suffixLayers)
        rowIndex colIndex
      = sldLayersDenote
          (sldAppendLayers (sldPadWindow padAboveCount padBelowCount rightWindow) suffixLayers)
          rowIndex colIndex := by
  have doesLeftPadReach : sldLayersTargetArityFrom
      (padAboveCount + (windowSourceArity + padBelowCount))
      (sldPadWindow padAboveCount padBelowCount leftWindow)
      = padAboveCount + (windowTargetArity + padBelowCount) := by
    rw [sldPadWindowTargetArityFrom padAboveCount padBelowCount leftWindow windowSourceArity,
      doesLeftReach]
  have doesRightPadReach : sldLayersTargetArityFrom
      (padAboveCount + (windowSourceArity + padBelowCount))
      (sldPadWindow padAboveCount padBelowCount rightWindow)
      = padAboveCount + (windowTargetArity + padBelowCount) := by
    rw [sldPadWindowTargetArityFrom padAboveCount padBelowCount rightWindow windowSourceArity,
      doesRightReach]
  refine Eq.trans (sldDenoteOfAppendAsProductEntry
    (sldPadWindow padAboveCount padBelowCount leftWindow)
    (padAboveCount + (windowSourceArity + padBelowCount)) suffixLayers rowIndex colIndex
    isColInside)
    (Eq.trans ?_ (sldDenoteOfAppendAsProductEntry
      (sldPadWindow padAboveCount padBelowCount rightWindow)
      (padAboveCount + (windowSourceArity + padBelowCount)) suffixLayers rowIndex colIndex
      isColInside).symm)
  rw [doesLeftPadReach, doesRightPadReach]
  exact sldProductRespectsEntryAgreement
    (padAboveCount + (windowTargetArity + padBelowCount))
    (sldLayersDenote suffixLayers) (sldLayersDenote suffixLayers)
    (sldLayersDenote (sldPadWindow padAboveCount padBelowCount leftWindow))
    (sldLayersDenote (sldPadWindow padAboveCount padBelowCount rightWindow))
    rowIndex colIndex
    (fun _ _ => rfl)
    (fun middleIndex isMiddleInside =>
      sldPaddedWindowsDenoteAgreeEntry padAboveCount padBelowCount leftWindow rightWindow
        windowSourceArity windowTargetArity isLeftComposable isRightComposable doesLeftReach
        doesRightReach doWindowsAgree middleIndex colIndex isMiddleInside isColInside)

/-! ## Split-move soundness: the block recombination lemmas -/

/-- Recombination, top-acts-first orientation: the two split stages multiply back to the
un-split layer (needs only the column bound). -/
theorem sldSplitTopFirstStagesRecombine (topCells bottomCells : SldLayer)
    (middleIndex colIndex : Nat)
    (isColInside : colIndex < sldLayerSourceArity topCells + sldLayerSourceArity bottomCells) :
    composeEntries (sldLayerTargetArity topCells + sldLayerSourceArity bottomCells)
        (sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity (sldLayerTargetArity topCells)) bottomCells))
        (sldLayerEntries
          (sldAppendCells topCells (sldWireLayerOfArity (sldLayerSourceArity bottomCells))))
        middleIndex colIndex
      = sldLayerEntries (sldAppendCells topCells bottomCells) middleIndex colIndex := by
  refine Eq.trans (sldProductRespectsEntryAgreement
    (sldLayerTargetArity topCells + sldLayerSourceArity bottomCells)
    (sldLayerEntries
      (sldAppendCells (sldWireLayerOfArity (sldLayerTargetArity topCells)) bottomCells))
    (directSumEntries (sldLayerTargetArity topCells) (sldLayerTargetArity topCells)
      identityEntries (sldLayerEntries bottomCells))
    (sldLayerEntries
      (sldAppendCells topCells (sldWireLayerOfArity (sldLayerSourceArity bottomCells))))
    (directSumEntries (sldLayerTargetArity topCells) (sldLayerSourceArity topCells)
      (sldLayerEntries topCells) identityEntries)
    middleIndex colIndex
    (fun innerIndex _ => by
      refine Eq.trans (sldAppendCellsEntriesAsBlocks
        (sldWireLayerOfArity (sldLayerTargetArity topCells)) bottomCells middleIndex
        innerIndex) ?_
      rw [sldWireLayerTargetArity, sldWireLayerSourceArity]
      exact sldDirectSumRespectsEntryAgreement (sldLayerTargetArity topCells)
        (sldLayerTargetArity topCells)
        (sldLayerEntries (sldWireLayerOfArity (sldLayerTargetArity topCells))) identityEntries
        (sldLayerEntries bottomCells) (sldLayerEntries bottomCells) middleIndex innerIndex
        (fun _ _ =>
          sldWireLayerEntriesAsIdentity (sldLayerTargetArity topCells) middleIndex innerIndex)
        (fun _ _ _ _ => rfl))
    (fun innerIndex _ => by
      refine Eq.trans (sldAppendCellsEntriesAsBlocks topCells
        (sldWireLayerOfArity (sldLayerSourceArity bottomCells)) innerIndex colIndex) ?_
      exact sldDirectSumRespectsEntryAgreement (sldLayerTargetArity topCells)
        (sldLayerSourceArity topCells)
        (sldLayerEntries topCells) (sldLayerEntries topCells)
        (sldLayerEntries (sldWireLayerOfArity (sldLayerSourceArity bottomCells)))
        identityEntries innerIndex colIndex
        (fun _ _ => rfl)
        (fun rowOffset colOffset _ _ =>
          sldWireLayerEntriesAsIdentity (sldLayerSourceArity bottomCells) rowOffset
            colOffset))) ?_
  refine Eq.trans (sldDirectSumMultiplicativityEntry (sldLayerTargetArity topCells)
    (sldLayerSourceArity bottomCells) (sldLayerTargetArity topCells)
    (sldLayerSourceArity topCells)
    identityEntries (sldLayerEntries bottomCells) (sldLayerEntries topCells) identityEntries
    middleIndex colIndex) ?_
  refine Eq.trans (sldDirectSumRespectsEntryAgreement (sldLayerTargetArity topCells)
    (sldLayerSourceArity topCells)
    (composeEntries (sldLayerTargetArity topCells) identityEntries (sldLayerEntries topCells))
    (sldLayerEntries topCells)
    (composeEntries (sldLayerSourceArity bottomCells) (sldLayerEntries bottomCells)
      identityEntries)
    (sldLayerEntries bottomCells)
    middleIndex colIndex
    (fun isRowInTop _ =>
      sldProductWithIdentityAfterCollapses (sldLayerTargetArity topCells)
        (sldLayerEntries topCells) middleIndex colIndex isRowInTop)
    (fun rowOffset colOffset _ doesColSplit => by
      refine sldProductWithIdentityBeforeCollapses (sldLayerSourceArity bottomCells)
        (sldLayerEntries bottomCells) rowOffset colOffset ?_
      rw [doesColSplit] at isColInside
      exact ltOfAddLtAddLeft (sldLayerSourceArity topCells) isColInside)) ?_
  exact (sldAppendCellsEntriesAsBlocks topCells bottomCells middleIndex colIndex).symm

/-- Recombination, bottom-acts-first orientation (needs the row bound instead). -/
theorem sldSplitBottomFirstStagesRecombine (topCells bottomCells : SldLayer)
    (middleIndex colIndex : Nat)
    (isMiddleInside :
      middleIndex < sldLayerTargetArity topCells + sldLayerTargetArity bottomCells) :
    composeEntries (sldLayerSourceArity topCells + sldLayerTargetArity bottomCells)
        (sldLayerEntries
          (sldAppendCells topCells (sldWireLayerOfArity (sldLayerTargetArity bottomCells))))
        (sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity (sldLayerSourceArity topCells)) bottomCells))
        middleIndex colIndex
      = sldLayerEntries (sldAppendCells topCells bottomCells) middleIndex colIndex := by
  refine Eq.trans (sldProductRespectsEntryAgreement
    (sldLayerSourceArity topCells + sldLayerTargetArity bottomCells)
    (sldLayerEntries
      (sldAppendCells topCells (sldWireLayerOfArity (sldLayerTargetArity bottomCells))))
    (directSumEntries (sldLayerTargetArity topCells) (sldLayerSourceArity topCells)
      (sldLayerEntries topCells) identityEntries)
    (sldLayerEntries
      (sldAppendCells (sldWireLayerOfArity (sldLayerSourceArity topCells)) bottomCells))
    (directSumEntries (sldLayerSourceArity topCells) (sldLayerSourceArity topCells)
      identityEntries (sldLayerEntries bottomCells))
    middleIndex colIndex
    (fun innerIndex _ => by
      refine Eq.trans (sldAppendCellsEntriesAsBlocks topCells
        (sldWireLayerOfArity (sldLayerTargetArity bottomCells)) middleIndex innerIndex) ?_
      exact sldDirectSumRespectsEntryAgreement (sldLayerTargetArity topCells)
        (sldLayerSourceArity topCells)
        (sldLayerEntries topCells) (sldLayerEntries topCells)
        (sldLayerEntries (sldWireLayerOfArity (sldLayerTargetArity bottomCells)))
        identityEntries middleIndex innerIndex
        (fun _ _ => rfl)
        (fun rowOffset colOffset _ _ =>
          sldWireLayerEntriesAsIdentity (sldLayerTargetArity bottomCells) rowOffset
            colOffset))
    (fun innerIndex _ => by
      refine Eq.trans (sldAppendCellsEntriesAsBlocks
        (sldWireLayerOfArity (sldLayerSourceArity topCells)) bottomCells innerIndex
        colIndex) ?_
      rw [sldWireLayerTargetArity, sldWireLayerSourceArity]
      exact sldDirectSumRespectsEntryAgreement (sldLayerSourceArity topCells)
        (sldLayerSourceArity topCells)
        (sldLayerEntries (sldWireLayerOfArity (sldLayerSourceArity topCells)))
        identityEntries
        (sldLayerEntries bottomCells) (sldLayerEntries bottomCells) innerIndex colIndex
        (fun _ _ =>
          sldWireLayerEntriesAsIdentity (sldLayerSourceArity topCells) innerIndex colIndex)
        (fun _ _ _ _ => rfl))) ?_
  refine Eq.trans (sldDirectSumMultiplicativityEntry (sldLayerSourceArity topCells)
    (sldLayerTargetArity bottomCells) (sldLayerTargetArity topCells)
    (sldLayerSourceArity topCells)
    (sldLayerEntries topCells) identityEntries identityEntries (sldLayerEntries bottomCells)
    middleIndex colIndex) ?_
  refine Eq.trans (sldDirectSumRespectsEntryAgreement (sldLayerTargetArity topCells)
    (sldLayerSourceArity topCells)
    (composeEntries (sldLayerSourceArity topCells) (sldLayerEntries topCells)
      identityEntries)
    (sldLayerEntries topCells)
    (composeEntries (sldLayerTargetArity bottomCells) identityEntries
      (sldLayerEntries bottomCells))
    (sldLayerEntries bottomCells)
    middleIndex colIndex
    (fun _ isColInTop =>
      sldProductWithIdentityBeforeCollapses (sldLayerSourceArity topCells)
        (sldLayerEntries topCells) middleIndex colIndex isColInTop)
    (fun rowOffset colOffset doesRowSplit _ => by
      refine sldProductWithIdentityAfterCollapses (sldLayerTargetArity bottomCells)
        (sldLayerEntries bottomCells) rowOffset colOffset ?_
      rw [doesRowSplit] at isMiddleInside
      exact ltOfAddLtAddLeft (sldLayerTargetArity topCells) isMiddleInside)) ?_
  exact (sldAppendCellsEntriesAsBlocks topCells bottomCells middleIndex colIndex).symm

/-! ## The 18 relation rows as layer windows

Left/right window pairs, transcribing the r1 `lafontRelationRows` into the strict-layer
carrier.  IDENTITY RIGHT SIDES ARE THE EMPTY LIST — the (co)unit and involution rows literally
DELETE layers, the honest strict-monoidal statement the binary syntax could not make. -/

/-- (M1) left: `(mu | wire) ; mu`. -/
def sldAddAssociativityLeftWindow : List SldLayer :=
  [[SldCell.generatorMu, SldCell.wire], [SldCell.generatorMu]]

/-- (M1) right: `(wire | mu) ; mu`. -/
def sldAddAssociativityRightWindow : List SldLayer :=
  [[SldCell.wire, SldCell.generatorMu], [SldCell.generatorMu]]

/-- (M2) left: `(eta | wire) ; mu`. -/
def sldAddLeftUnitLeftWindow : List SldLayer :=
  [[SldCell.generatorEta, SldCell.wire], [SldCell.generatorMu]]

/-- (M2) right: the EMPTY window — the identity is absent syntax. -/
def sldAddLeftUnitRightWindow : List SldLayer := []

/-- (M3) left: `(wire | eta) ; mu` — the r30 refuted unit pair's shape. -/
def sldAddRightUnitLeftWindow : List SldLayer :=
  [[SldCell.wire, SldCell.generatorEta], [SldCell.generatorMu]]

/-- (M3) right: empty. -/
def sldAddRightUnitRightWindow : List SldLayer := []

/-- (M4) left: `tau ; mu`. -/
def sldAddCommutativityLeftWindow : List SldLayer :=
  [[SldCell.crossing], [SldCell.generatorMu]]

/-- (M4) right: bare `mu`. -/
def sldAddCommutativityRightWindow : List SldLayer := [[SldCell.generatorMu]]

/-- (C1) left: `delta ; (delta | wire)`. -/
def sldCopyCoassociativityLeftWindow : List SldLayer :=
  [[SldCell.generatorDelta], [SldCell.generatorDelta, SldCell.wire]]

/-- (C1) right: `delta ; (wire | delta)`. -/
def sldCopyCoassociativityRightWindow : List SldLayer :=
  [[SldCell.generatorDelta], [SldCell.wire, SldCell.generatorDelta]]

/-- (C2) left: `delta ; (epsilon | wire)`. -/
def sldCopyLeftCounitLeftWindow : List SldLayer :=
  [[SldCell.generatorDelta], [SldCell.generatorEpsilon, SldCell.wire]]

/-- (C2) right: empty. -/
def sldCopyLeftCounitRightWindow : List SldLayer := []

/-- (C3) left: `delta ; (wire | epsilon)`. -/
def sldCopyRightCounitLeftWindow : List SldLayer :=
  [[SldCell.generatorDelta], [SldCell.wire, SldCell.generatorEpsilon]]

/-- (C3) right: empty. -/
def sldCopyRightCounitRightWindow : List SldLayer := []

/-- (C4) left: `delta ; tau`. -/
def sldCopyCocommutativityLeftWindow : List SldLayer :=
  [[SldCell.generatorDelta], [SldCell.crossing]]

/-- (C4) right: bare `delta`. -/
def sldCopyCocommutativityRightWindow : List SldLayer := [[SldCell.generatorDelta]]

/-- (B1) left: `mu ; delta`. -/
def sldBimonoidSquareLeftWindow : List SldLayer :=
  [[SldCell.generatorMu], [SldCell.generatorDelta]]

/-- (B1) right: `(delta | delta) ; (wire | tau | wire) ; (mu | mu)`. -/
def sldBimonoidSquareRightWindow : List SldLayer :=
  [[SldCell.generatorDelta, SldCell.generatorDelta],
   [SldCell.wire, SldCell.crossing, SldCell.wire],
   [SldCell.generatorMu, SldCell.generatorMu]]

/-- (B2) left: `eta ; delta`. -/
def sldCopyAfterZeroLeftWindow : List SldLayer :=
  [[SldCell.generatorEta], [SldCell.generatorDelta]]

/-- (B2) right: `eta | eta` — ONE layer, the carrier's native tensor. -/
def sldCopyAfterZeroRightWindow : List SldLayer :=
  [[SldCell.generatorEta, SldCell.generatorEta]]

/-- (B3) left: `mu ; epsilon`. -/
def sldDiscardAfterAddLeftWindow : List SldLayer :=
  [[SldCell.generatorMu], [SldCell.generatorEpsilon]]

/-- (B3) right: `epsilon | epsilon`. -/
def sldDiscardAfterAddRightWindow : List SldLayer :=
  [[SldCell.generatorEpsilon, SldCell.generatorEpsilon]]

/-- (B4) left: `eta ; epsilon` — the closed loop. -/
def sldDiscardAfterZeroLeftWindow : List SldLayer :=
  [[SldCell.generatorEta], [SldCell.generatorEpsilon]]

/-- (B4) right: empty — the closed loop DIES into no syntax at all. -/
def sldDiscardAfterZeroRightWindow : List SldLayer := []

/-- (S1) left: `tau ; tau`. -/
def sldSwapInvolutionLeftWindow : List SldLayer :=
  [[SldCell.crossing], [SldCell.crossing]]

/-- (S1) right: empty (id2 is absent syntax). -/
def sldSwapInvolutionRightWindow : List SldLayer := []

/-- (S2) left: `(tau | wire) ; (wire | tau) ; (tau | wire)`. -/
def sldSwapYangBaxterLeftWindow : List SldLayer :=
  [[SldCell.crossing, SldCell.wire], [SldCell.wire, SldCell.crossing],
   [SldCell.crossing, SldCell.wire]]

/-- (S2) right: `(wire | tau) ; (tau | wire) ; (wire | tau)`. -/
def sldSwapYangBaxterRightWindow : List SldLayer :=
  [[SldCell.wire, SldCell.crossing], [SldCell.crossing, SldCell.wire],
   [SldCell.wire, SldCell.crossing]]

/-- (Nmu) left: `(mu | wire) ; tau`. -/
def sldSwapPastAddLeftWindow : List SldLayer :=
  [[SldCell.generatorMu, SldCell.wire], [SldCell.crossing]]

/-- (Nmu) right: `(wire | tau) ; (tau | wire) ; (wire | mu)`. -/
def sldSwapPastAddRightWindow : List SldLayer :=
  [[SldCell.wire, SldCell.crossing], [SldCell.crossing, SldCell.wire],
   [SldCell.wire, SldCell.generatorMu]]

/-- (Neta) left: `(eta | wire) ; tau`. -/
def sldSwapPastZeroLeftWindow : List SldLayer :=
  [[SldCell.generatorEta, SldCell.wire], [SldCell.crossing]]

/-- (Neta) right: `wire | eta`. -/
def sldSwapPastZeroRightWindow : List SldLayer :=
  [[SldCell.wire, SldCell.generatorEta]]

/-- (Ndelta) left: `tau ; (delta | wire)`. -/
def sldCopyPastSwapLeftWindow : List SldLayer :=
  [[SldCell.crossing], [SldCell.generatorDelta, SldCell.wire]]

/-- (Ndelta) right: `(wire | delta) ; (tau | wire) ; (wire | tau)`. -/
def sldCopyPastSwapRightWindow : List SldLayer :=
  [[SldCell.wire, SldCell.generatorDelta], [SldCell.crossing, SldCell.wire],
   [SldCell.wire, SldCell.crossing]]

/-- (Neps) left: `tau ; (epsilon | wire)`. -/
def sldDiscardPastSwapLeftWindow : List SldLayer :=
  [[SldCell.crossing], [SldCell.generatorEpsilon, SldCell.wire]]

/-- (Neps) right: `wire | epsilon`. -/
def sldDiscardPastSwapRightWindow : List SldLayer :=
  [[SldCell.wire, SldCell.generatorEpsilon]]

/-- Row coherence: both windows composable from the source boundary, both reaching the target
boundary, denotations agreeing on the window rectangle. -/
def sldDoRowWindowsCohere (windowSourceArity windowTargetArity : Nat)
    (leftWindow rightWindow : List SldLayer) : Bool :=
  sldLayersAreComposableFrom windowSourceArity leftWindow
    && sldLayersAreComposableFrom windowSourceArity rightWindow
    && Nat.beq (sldLayersTargetArityFrom windowSourceArity leftWindow) windowTargetArity
    && Nat.beq (sldLayersTargetArityFrom windowSourceArity rightWindow) windowTargetArity
    && doEntriesAgreeUpTo windowTargetArity windowSourceArity
        (sldLayersDenote leftWindow) (sldLayersDenote rightWindow)

/-- THE ROW GATE (kernel `rfl`): all 18 window pairs cohere — composable, boundary-exact, and
Mat(N)-sound. -/
theorem sldAllEighteenRowWindowsCohere :
    (sldDoRowWindowsCohere 3 1 sldAddAssociativityLeftWindow sldAddAssociativityRightWindow
      && sldDoRowWindowsCohere 1 1 sldAddLeftUnitLeftWindow sldAddLeftUnitRightWindow
      && sldDoRowWindowsCohere 1 1 sldAddRightUnitLeftWindow sldAddRightUnitRightWindow
      && sldDoRowWindowsCohere 2 1 sldAddCommutativityLeftWindow
          sldAddCommutativityRightWindow
      && sldDoRowWindowsCohere 1 3 sldCopyCoassociativityLeftWindow
          sldCopyCoassociativityRightWindow
      && sldDoRowWindowsCohere 1 1 sldCopyLeftCounitLeftWindow sldCopyLeftCounitRightWindow
      && sldDoRowWindowsCohere 1 1 sldCopyRightCounitLeftWindow sldCopyRightCounitRightWindow
      && sldDoRowWindowsCohere 1 2 sldCopyCocommutativityLeftWindow
          sldCopyCocommutativityRightWindow
      && sldDoRowWindowsCohere 2 2 sldBimonoidSquareLeftWindow sldBimonoidSquareRightWindow
      && sldDoRowWindowsCohere 0 2 sldCopyAfterZeroLeftWindow sldCopyAfterZeroRightWindow
      && sldDoRowWindowsCohere 2 0 sldDiscardAfterAddLeftWindow
          sldDiscardAfterAddRightWindow
      && sldDoRowWindowsCohere 0 0 sldDiscardAfterZeroLeftWindow
          sldDiscardAfterZeroRightWindow
      && sldDoRowWindowsCohere 2 2 sldSwapInvolutionLeftWindow sldSwapInvolutionRightWindow
      && sldDoRowWindowsCohere 3 3 sldSwapYangBaxterLeftWindow sldSwapYangBaxterRightWindow
      && sldDoRowWindowsCohere 3 2 sldSwapPastAddLeftWindow sldSwapPastAddRightWindow
      && sldDoRowWindowsCohere 1 2 sldSwapPastZeroLeftWindow sldSwapPastZeroRightWindow
      && sldDoRowWindowsCohere 2 3 sldCopyPastSwapLeftWindow sldCopyPastSwapRightWindow
      && sldDoRowWindowsCohere 2 1 sldDiscardPastSwapLeftWindow
          sldDiscardPastSwapRightWindow) = true := rfl

/-! ## The congruence: boundary-indexed convertibility of layer lists -/

/-- Convertibility of layer lists at a source boundary: groupoid closure, congruence under a
leading layer, the two layer-split moves, and the 18 relation rows fired through
`sldPadWindow` at any pad and any suffix.  The boundary index pins each leaf move's source
arity — the well-formedness discipline that replaces the old syntax's dependent typing. -/
inductive SldAreConvertibleLayers : Nat -> List SldLayer -> List SldLayer -> Prop where
  | fromReflexivity (boundaryArity : Nat) (layers : List SldLayer) :
      SldAreConvertibleLayers boundaryArity layers layers
  | fromSymmetry {boundaryArity : Nat} {leftLayers rightLayers : List SldLayer} :
      SldAreConvertibleLayers boundaryArity leftLayers rightLayers ->
      SldAreConvertibleLayers boundaryArity rightLayers leftLayers
  | fromTransitivity {boundaryArity : Nat}
      {leftLayers middleLayers rightLayers : List SldLayer} :
      SldAreConvertibleLayers boundaryArity leftLayers middleLayers ->
      SldAreConvertibleLayers boundaryArity middleLayers rightLayers ->
      SldAreConvertibleLayers boundaryArity leftLayers rightLayers
  | underLayerPrefix (boundaryArity : Nat) (contextLayer : SldLayer)
      {tailLeft tailRight : List SldLayer} :
      SldAreConvertibleLayers (sldLayerTargetArity contextLayer) tailLeft tailRight ->
      SldAreConvertibleLayers boundaryArity (contextLayer :: tailLeft)
        (contextLayer :: tailRight)
  | layerSplitTopActsFirst (topCells bottomCells : SldLayer) (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (sldLayerSourceArity (sldAppendCells topCells bottomCells))
        (sldAppendCells topCells bottomCells :: suffixLayers)
        (sldAppendCells topCells (sldWireLayerOfArity (sldLayerSourceArity bottomCells))
          :: sldAppendCells (sldWireLayerOfArity (sldLayerTargetArity topCells)) bottomCells
          :: suffixLayers)
  | layerSplitBottomActsFirst (topCells bottomCells : SldLayer)
      (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (sldLayerSourceArity (sldAppendCells topCells bottomCells))
        (sldAppendCells topCells bottomCells :: suffixLayers)
        (sldAppendCells (sldWireLayerOfArity (sldLayerSourceArity topCells)) bottomCells
          :: sldAppendCells topCells (sldWireLayerOfArity (sldLayerTargetArity bottomCells))
          :: suffixLayers)
  | fromAddAssociativityRow (padAboveCount padBelowCount : Nat)
      (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (3 + padBelowCount))
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldAddAssociativityLeftWindow)
          suffixLayers)
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldAddAssociativityRightWindow)
          suffixLayers)
  | fromAddLeftUnitRow (padAboveCount padBelowCount : Nat) (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (1 + padBelowCount))
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldAddLeftUnitLeftWindow)
          suffixLayers)
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldAddLeftUnitRightWindow)
          suffixLayers)
  | fromAddRightUnitRow (padAboveCount padBelowCount : Nat) (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (1 + padBelowCount))
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldAddRightUnitLeftWindow)
          suffixLayers)
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldAddRightUnitRightWindow)
          suffixLayers)
  | fromAddCommutativityRow (padAboveCount padBelowCount : Nat)
      (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (2 + padBelowCount))
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldAddCommutativityLeftWindow)
          suffixLayers)
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldAddCommutativityRightWindow)
          suffixLayers)
  | fromCopyCoassociativityRow (padAboveCount padBelowCount : Nat)
      (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (1 + padBelowCount))
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldCopyCoassociativityLeftWindow)
          suffixLayers)
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldCopyCoassociativityRightWindow)
          suffixLayers)
  | fromCopyLeftCounitRow (padAboveCount padBelowCount : Nat)
      (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (1 + padBelowCount))
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldCopyLeftCounitLeftWindow)
          suffixLayers)
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldCopyLeftCounitRightWindow)
          suffixLayers)
  | fromCopyRightCounitRow (padAboveCount padBelowCount : Nat)
      (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (1 + padBelowCount))
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldCopyRightCounitLeftWindow)
          suffixLayers)
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldCopyRightCounitRightWindow)
          suffixLayers)
  | fromCopyCocommutativityRow (padAboveCount padBelowCount : Nat)
      (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (1 + padBelowCount))
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldCopyCocommutativityLeftWindow)
          suffixLayers)
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldCopyCocommutativityRightWindow)
          suffixLayers)
  | fromBimonoidSquareRow (padAboveCount padBelowCount : Nat)
      (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (2 + padBelowCount))
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldBimonoidSquareLeftWindow)
          suffixLayers)
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldBimonoidSquareRightWindow)
          suffixLayers)
  | fromCopyAfterZeroRow (padAboveCount padBelowCount : Nat) (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (0 + padBelowCount))
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldCopyAfterZeroLeftWindow)
          suffixLayers)
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldCopyAfterZeroRightWindow)
          suffixLayers)
  | fromDiscardAfterAddRow (padAboveCount padBelowCount : Nat)
      (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (2 + padBelowCount))
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldDiscardAfterAddLeftWindow)
          suffixLayers)
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldDiscardAfterAddRightWindow)
          suffixLayers)
  | fromDiscardAfterZeroRow (padAboveCount padBelowCount : Nat)
      (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (0 + padBelowCount))
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldDiscardAfterZeroLeftWindow)
          suffixLayers)
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldDiscardAfterZeroRightWindow)
          suffixLayers)
  | fromSwapInvolutionRow (padAboveCount padBelowCount : Nat)
      (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (2 + padBelowCount))
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldSwapInvolutionLeftWindow)
          suffixLayers)
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldSwapInvolutionRightWindow)
          suffixLayers)
  | fromSwapYangBaxterRow (padAboveCount padBelowCount : Nat)
      (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (3 + padBelowCount))
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldSwapYangBaxterLeftWindow)
          suffixLayers)
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldSwapYangBaxterRightWindow)
          suffixLayers)
  | fromSwapPastAddRow (padAboveCount padBelowCount : Nat) (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (3 + padBelowCount))
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldSwapPastAddLeftWindow)
          suffixLayers)
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldSwapPastAddRightWindow)
          suffixLayers)
  | fromSwapPastZeroRow (padAboveCount padBelowCount : Nat) (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (1 + padBelowCount))
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldSwapPastZeroLeftWindow)
          suffixLayers)
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldSwapPastZeroRightWindow)
          suffixLayers)
  | fromCopyPastSwapRow (padAboveCount padBelowCount : Nat) (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (2 + padBelowCount))
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldCopyPastSwapLeftWindow)
          suffixLayers)
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount sldCopyPastSwapRightWindow)
          suffixLayers)
  | fromDiscardPastSwapRow (padAboveCount padBelowCount : Nat)
      (suffixLayers : List SldLayer) :
      SldAreConvertibleLayers (padAboveCount + (2 + padBelowCount))
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldDiscardPastSwapLeftWindow)
          suffixLayers)
        (sldAppendLayers
          (sldPadWindow padAboveCount padBelowCount sldDiscardPastSwapRightWindow)
          suffixLayers)

/-- THE DERIVED EXCHANGE ([DelpeuchVicary2018]'s move): two cells in adjacent layers on
disjoint strand blocks commute — one split forward, the other backward. -/
theorem sldDisjointLayersExchange (topCells bottomCells : SldLayer)
    (suffixLayers : List SldLayer) :
    SldAreConvertibleLayers (sldLayerSourceArity (sldAppendCells topCells bottomCells))
      (sldAppendCells topCells (sldWireLayerOfArity (sldLayerSourceArity bottomCells))
        :: sldAppendCells (sldWireLayerOfArity (sldLayerTargetArity topCells)) bottomCells
        :: suffixLayers)
      (sldAppendCells (sldWireLayerOfArity (sldLayerSourceArity topCells)) bottomCells
        :: sldAppendCells topCells (sldWireLayerOfArity (sldLayerTargetArity bottomCells))
        :: suffixLayers) :=
  SldAreConvertibleLayers.fromTransitivity
    (SldAreConvertibleLayers.fromSymmetry
      (SldAreConvertibleLayers.layerSplitTopActsFirst topCells bottomCells suffixLayers))
    (SldAreConvertibleLayers.layerSplitBottomActsFirst topCells bottomCells suffixLayers)

/-! ## Soundness of the congruence -/

/-- Target-arity preservation: convertible layer lists reach the same boundary. -/
theorem sldConvertibleLayersKeepTargetArity {boundaryArity : Nat}
    {leftLayers rightLayers : List SldLayer}
    (areConvertible : SldAreConvertibleLayers boundaryArity leftLayers rightLayers) :
    sldLayersTargetArityFrom boundaryArity leftLayers
      = sldLayersTargetArityFrom boundaryArity rightLayers := by
  induction areConvertible with
  | fromReflexivity _ _ => rfl
  | fromSymmetry _ flippedEq => exact flippedEq.symm
  | fromTransitivity _ _ leftEq rightEq => exact leftEq.trans rightEq
  | underLayerPrefix _ contextLayer _ tailEq => exact tailEq
  | layerSplitTopActsFirst topCells bottomCells suffixLayers =>
      show sldLayersTargetArityFrom
          (sldLayerTargetArity (sldAppendCells topCells bottomCells)) suffixLayers
        = sldLayersTargetArityFrom
            (sldLayerTargetArity
              (sldAppendCells (sldWireLayerOfArity (sldLayerTargetArity topCells))
                bottomCells)) suffixLayers
      rw [sldAppendCellsTargetArity topCells bottomCells,
        sldAppendCellsTargetArity (sldWireLayerOfArity (sldLayerTargetArity topCells))
          bottomCells,
        sldWireLayerTargetArity]
  | layerSplitBottomActsFirst topCells bottomCells suffixLayers =>
      show sldLayersTargetArityFrom
          (sldLayerTargetArity (sldAppendCells topCells bottomCells)) suffixLayers
        = sldLayersTargetArityFrom
            (sldLayerTargetArity
              (sldAppendCells topCells
                (sldWireLayerOfArity (sldLayerTargetArity bottomCells)))) suffixLayers
      rw [sldAppendCellsTargetArity topCells bottomCells,
        sldAppendCellsTargetArity topCells
          (sldWireLayerOfArity (sldLayerTargetArity bottomCells)),
        sldWireLayerTargetArity]
  | fromAddAssociativityRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldAddAssociativityLeftWindow 3,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldAddAssociativityRightWindow 3]
      rfl
  | fromAddLeftUnitRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount sldAddLeftUnitLeftWindow 1,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount sldAddLeftUnitRightWindow 1]
      rfl
  | fromAddRightUnitRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount sldAddRightUnitLeftWindow 1,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount sldAddRightUnitRightWindow 1]
      rfl
  | fromAddCommutativityRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldAddCommutativityLeftWindow 2,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldAddCommutativityRightWindow 2]
      rfl
  | fromCopyCoassociativityRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldCopyCoassociativityLeftWindow 1,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldCopyCoassociativityRightWindow 1]
      rfl
  | fromCopyLeftCounitRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount sldCopyLeftCounitLeftWindow 1,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldCopyLeftCounitRightWindow 1]
      rfl
  | fromCopyRightCounitRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldCopyRightCounitLeftWindow 1,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldCopyRightCounitRightWindow 1]
      rfl
  | fromCopyCocommutativityRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldCopyCocommutativityLeftWindow 1,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldCopyCocommutativityRightWindow 1]
      rfl
  | fromBimonoidSquareRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount sldBimonoidSquareLeftWindow 2,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldBimonoidSquareRightWindow 2]
      rfl
  | fromCopyAfterZeroRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount sldCopyAfterZeroLeftWindow 0,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldCopyAfterZeroRightWindow 0]
      rfl
  | fromDiscardAfterAddRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldDiscardAfterAddLeftWindow 2,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldDiscardAfterAddRightWindow 2]
      rfl
  | fromDiscardAfterZeroRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldDiscardAfterZeroLeftWindow 0,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldDiscardAfterZeroRightWindow 0]
      rfl
  | fromSwapInvolutionRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldSwapInvolutionLeftWindow 2,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldSwapInvolutionRightWindow 2]
      rfl
  | fromSwapYangBaxterRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldSwapYangBaxterLeftWindow 3,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldSwapYangBaxterRightWindow 3]
      rfl
  | fromSwapPastAddRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount sldSwapPastAddLeftWindow 3,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount sldSwapPastAddRightWindow 3]
      rfl
  | fromSwapPastZeroRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount sldSwapPastZeroLeftWindow 1,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount sldSwapPastZeroRightWindow 1]
      rfl
  | fromCopyPastSwapRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount sldCopyPastSwapLeftWindow 2,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount sldCopyPastSwapRightWindow 2]
      rfl
  | fromDiscardPastSwapRow padAboveCount padBelowCount suffixLayers =>
      rw [sldAppendLayersTargetArityFrom, sldAppendLayersTargetArityFrom,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldDiscardPastSwapLeftWindow 2,
        sldPadWindowTargetArityFrom padAboveCount padBelowCount
          sldDiscardPastSwapRightWindow 2]
      rfl

/-- SOUNDNESS: convertible layer lists denote EQUAL matrices at every row and every column
inside the source boundary — one induction, rows through the pad engine, splits through the
recombination lemmas. -/
theorem sldConvertibleLayersDenoteEqualEntries {boundaryArity : Nat}
    {leftLayers rightLayers : List SldLayer}
    (areConvertible : SldAreConvertibleLayers boundaryArity leftLayers rightLayers) :
    ∀ rowIndex colIndex, colIndex < boundaryArity ->
      sldLayersDenote leftLayers rowIndex colIndex
        = sldLayersDenote rightLayers rowIndex colIndex := by
  induction areConvertible with
  | fromReflexivity _ _ => exact fun _ _ _ => rfl
  | fromSymmetry _ flippedAgree =>
      exact fun rowIndex colIndex isColInside =>
        (flippedAgree rowIndex colIndex isColInside).symm
  | fromTransitivity _ _ leftAgree rightAgree =>
      exact fun rowIndex colIndex isColInside =>
        (leftAgree rowIndex colIndex isColInside).trans
          (rightAgree rowIndex colIndex isColInside)
  | underLayerPrefix _ contextLayer _ tailAgree =>
      intro rowIndex colIndex _
      exact sldProductRespectsEntryAgreement (sldLayerTargetArity contextLayer) _ _
        (sldLayerEntries contextLayer) (sldLayerEntries contextLayer) rowIndex colIndex
        (fun middleIndex isMiddleInside => tailAgree rowIndex middleIndex isMiddleInside)
        (fun _ _ => rfl)
  | layerSplitTopActsFirst topCells bottomCells suffixLayers =>
      intro rowIndex colIndex isColInside
      rw [sldAppendCellsSourceArity] at isColInside
      show composeEntries (sldLayerTargetArity (sldAppendCells topCells bottomCells))
          (sldLayersDenote suffixLayers)
          (sldLayerEntries (sldAppendCells topCells bottomCells)) rowIndex colIndex
        = composeEntries
            (sldLayerTargetArity
              (sldAppendCells topCells
                (sldWireLayerOfArity (sldLayerSourceArity bottomCells))))
            (composeEntries
              (sldLayerTargetArity
                (sldAppendCells (sldWireLayerOfArity (sldLayerTargetArity topCells))
                  bottomCells))
              (sldLayersDenote suffixLayers)
              (sldLayerEntries
                (sldAppendCells (sldWireLayerOfArity (sldLayerTargetArity topCells))
                  bottomCells)))
            (sldLayerEntries
              (sldAppendCells topCells
                (sldWireLayerOfArity (sldLayerSourceArity bottomCells))))
            rowIndex colIndex
      rw [sldAppendCellsTargetArity topCells bottomCells,
        sldAppendCellsTargetArity topCells
          (sldWireLayerOfArity (sldLayerSourceArity bottomCells)),
        sldWireLayerTargetArity,
        sldAppendCellsTargetArity (sldWireLayerOfArity (sldLayerTargetArity topCells))
          bottomCells,
        sldWireLayerTargetArity]
      refine Eq.trans ?_ (sldProductAssocEntry
        (sldLayerTargetArity topCells + sldLayerSourceArity bottomCells)
        (sldLayerTargetArity topCells + sldLayerTargetArity bottomCells)
        (sldLayersDenote suffixLayers)
        (sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity (sldLayerTargetArity topCells)) bottomCells))
        (sldLayerEntries
          (sldAppendCells topCells (sldWireLayerOfArity (sldLayerSourceArity bottomCells))))
        rowIndex colIndex)
      exact sldProductRespectsEntryAgreement
        (sldLayerTargetArity topCells + sldLayerTargetArity bottomCells)
        (sldLayersDenote suffixLayers) (sldLayersDenote suffixLayers)
        (sldLayerEntries (sldAppendCells topCells bottomCells))
        (composeEntries (sldLayerTargetArity topCells + sldLayerSourceArity bottomCells)
          (sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity (sldLayerTargetArity topCells)) bottomCells))
          (sldLayerEntries
            (sldAppendCells topCells
              (sldWireLayerOfArity (sldLayerSourceArity bottomCells)))))
        rowIndex colIndex
        (fun _ _ => rfl)
        (fun middleIndex _ =>
          (sldSplitTopFirstStagesRecombine topCells bottomCells middleIndex colIndex
            isColInside).symm)
  | layerSplitBottomActsFirst topCells bottomCells suffixLayers =>
      intro rowIndex colIndex isColInside
      rw [sldAppendCellsSourceArity] at isColInside
      show composeEntries (sldLayerTargetArity (sldAppendCells topCells bottomCells))
          (sldLayersDenote suffixLayers)
          (sldLayerEntries (sldAppendCells topCells bottomCells)) rowIndex colIndex
        = composeEntries
            (sldLayerTargetArity
              (sldAppendCells (sldWireLayerOfArity (sldLayerSourceArity topCells))
                bottomCells))
            (composeEntries
              (sldLayerTargetArity
                (sldAppendCells topCells
                  (sldWireLayerOfArity (sldLayerTargetArity bottomCells))))
              (sldLayersDenote suffixLayers)
              (sldLayerEntries
                (sldAppendCells topCells
                  (sldWireLayerOfArity (sldLayerTargetArity bottomCells)))))
            (sldLayerEntries
              (sldAppendCells (sldWireLayerOfArity (sldLayerSourceArity topCells))
                bottomCells))
            rowIndex colIndex
      rw [sldAppendCellsTargetArity topCells bottomCells,
        sldAppendCellsTargetArity (sldWireLayerOfArity (sldLayerSourceArity topCells))
          bottomCells,
        sldWireLayerTargetArity,
        sldAppendCellsTargetArity topCells
          (sldWireLayerOfArity (sldLayerTargetArity bottomCells)),
        sldWireLayerTargetArity]
      refine Eq.trans ?_ (sldProductAssocEntry
        (sldLayerSourceArity topCells + sldLayerTargetArity bottomCells)
        (sldLayerTargetArity topCells + sldLayerTargetArity bottomCells)
        (sldLayersDenote suffixLayers)
        (sldLayerEntries
          (sldAppendCells topCells (sldWireLayerOfArity (sldLayerTargetArity bottomCells))))
        (sldLayerEntries
          (sldAppendCells (sldWireLayerOfArity (sldLayerSourceArity topCells)) bottomCells))
        rowIndex colIndex)
      exact sldProductRespectsEntryAgreement
        (sldLayerTargetArity topCells + sldLayerTargetArity bottomCells)
        (sldLayersDenote suffixLayers) (sldLayersDenote suffixLayers)
        (sldLayerEntries (sldAppendCells topCells bottomCells))
        (composeEntries (sldLayerSourceArity topCells + sldLayerTargetArity bottomCells)
          (sldLayerEntries
            (sldAppendCells topCells
              (sldWireLayerOfArity (sldLayerTargetArity bottomCells))))
          (sldLayerEntries
            (sldAppendCells (sldWireLayerOfArity (sldLayerSourceArity topCells))
              bottomCells)))
        rowIndex colIndex
        (fun _ _ => rfl)
        (fun middleIndex isMiddleInside =>
          (sldSplitBottomFirstStagesRecombine topCells bottomCells middleIndex colIndex
            isMiddleInside).symm)
  | fromAddAssociativityRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldAddAssociativityLeftWindow
          sldAddAssociativityRightWindow 3 1 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 1 3 (sldLayersDenote sldAddAssociativityLeftWindow)
            (sldLayersDenote sldAddAssociativityRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromAddLeftUnitRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldAddLeftUnitLeftWindow
          sldAddLeftUnitRightWindow 1 1 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 1 1 (sldLayersDenote sldAddLeftUnitLeftWindow)
            (sldLayersDenote sldAddLeftUnitRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromAddRightUnitRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldAddRightUnitLeftWindow
          sldAddRightUnitRightWindow 1 1 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 1 1 (sldLayersDenote sldAddRightUnitLeftWindow)
            (sldLayersDenote sldAddRightUnitRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromAddCommutativityRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldAddCommutativityLeftWindow
          sldAddCommutativityRightWindow 2 1 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 1 2 (sldLayersDenote sldAddCommutativityLeftWindow)
            (sldLayersDenote sldAddCommutativityRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromCopyCoassociativityRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldCopyCoassociativityLeftWindow
          sldCopyCoassociativityRightWindow 1 3 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 3 1 (sldLayersDenote sldCopyCoassociativityLeftWindow)
            (sldLayersDenote sldCopyCoassociativityRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromCopyLeftCounitRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldCopyLeftCounitLeftWindow
          sldCopyLeftCounitRightWindow 1 1 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 1 1 (sldLayersDenote sldCopyLeftCounitLeftWindow)
            (sldLayersDenote sldCopyLeftCounitRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromCopyRightCounitRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldCopyRightCounitLeftWindow
          sldCopyRightCounitRightWindow 1 1 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 1 1 (sldLayersDenote sldCopyRightCounitLeftWindow)
            (sldLayersDenote sldCopyRightCounitRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromCopyCocommutativityRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldCopyCocommutativityLeftWindow
          sldCopyCocommutativityRightWindow 1 2 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 2 1 (sldLayersDenote sldCopyCocommutativityLeftWindow)
            (sldLayersDenote sldCopyCocommutativityRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromBimonoidSquareRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldBimonoidSquareLeftWindow
          sldBimonoidSquareRightWindow 2 2 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 2 2 (sldLayersDenote sldBimonoidSquareLeftWindow)
            (sldLayersDenote sldBimonoidSquareRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromCopyAfterZeroRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldCopyAfterZeroLeftWindow
          sldCopyAfterZeroRightWindow 0 2 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 2 0 (sldLayersDenote sldCopyAfterZeroLeftWindow)
            (sldLayersDenote sldCopyAfterZeroRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromDiscardAfterAddRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldDiscardAfterAddLeftWindow
          sldDiscardAfterAddRightWindow 2 0 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 0 2 (sldLayersDenote sldDiscardAfterAddLeftWindow)
            (sldLayersDenote sldDiscardAfterAddRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromDiscardAfterZeroRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldDiscardAfterZeroLeftWindow
          sldDiscardAfterZeroRightWindow 0 0 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 0 0 (sldLayersDenote sldDiscardAfterZeroLeftWindow)
            (sldLayersDenote sldDiscardAfterZeroRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromSwapInvolutionRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldSwapInvolutionLeftWindow
          sldSwapInvolutionRightWindow 2 2 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 2 2 (sldLayersDenote sldSwapInvolutionLeftWindow)
            (sldLayersDenote sldSwapInvolutionRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromSwapYangBaxterRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldSwapYangBaxterLeftWindow
          sldSwapYangBaxterRightWindow 3 3 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 3 3 (sldLayersDenote sldSwapYangBaxterLeftWindow)
            (sldLayersDenote sldSwapYangBaxterRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromSwapPastAddRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldSwapPastAddLeftWindow
          sldSwapPastAddRightWindow 3 2 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 2 3 (sldLayersDenote sldSwapPastAddLeftWindow)
            (sldLayersDenote sldSwapPastAddRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromSwapPastZeroRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldSwapPastZeroLeftWindow
          sldSwapPastZeroRightWindow 1 2 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 2 1 (sldLayersDenote sldSwapPastZeroLeftWindow)
            (sldLayersDenote sldSwapPastZeroRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromCopyPastSwapRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldCopyPastSwapLeftWindow
          sldCopyPastSwapRightWindow 2 3 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 3 2 (sldLayersDenote sldCopyPastSwapLeftWindow)
            (sldLayersDenote sldCopyPastSwapRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside
  | fromDiscardPastSwapRow padAboveCount padBelowCount suffixLayers =>
      exact fun rowIndex colIndex isColInside =>
        sldPaddedRowRewritePreservesDenoteEntry sldDiscardPastSwapLeftWindow
          sldDiscardPastSwapRightWindow 2 1 rfl rfl rfl rfl
          (pointwiseOfAgreeUpTo 1 2 (sldLayersDenote sldDiscardPastSwapLeftWindow)
            (sldLayersDenote sldDiscardPastSwapRightWindow) rfl)
          padAboveCount padBelowCount suffixLayers rowIndex colIndex isColInside

/-- Bool form of soundness on any rectangle over the source boundary. -/
theorem sldConvertibleLayersDenoteAgreeUpTo {boundaryArity : Nat}
    {leftLayers rightLayers : List SldLayer}
    (areConvertible : SldAreConvertibleLayers boundaryArity leftLayers rightLayers)
    (rowBound : Nat) :
    doEntriesAgreeUpTo rowBound boundaryArity (sldLayersDenote leftLayers)
      (sldLayersDenote rightLayers) = true :=
  agreeUpToOfPointwise rowBound boundaryArity (sldLayersDenote leftLayers)
    (sldLayersDenote rightLayers)
    (fun rowIndex colIndex _ isColInside =>
      sldConvertibleLayersDenoteEqualEntries areConvertible rowIndex colIndex isColInside)

/-- THE NEGATIVE DECISION DIRECTION: layer lists with different matrices are NOT convertible. -/
theorem sldNotConvertibleOfDistinctDenotes {boundaryArity : Nat}
    (leftLayers rightLayers : List SldLayer) (rowBound : Nat)
    (doDenotesDiffer : doEntriesAgreeUpTo rowBound boundaryArity
      (sldLayersDenote leftLayers) (sldLayersDenote rightLayers) = false) :
    SldAreConvertibleLayers boundaryArity leftLayers rightLayers -> False :=
  fun areConvertible =>
    Bool.noConfusion
      (doDenotesDiffer.symm.trans
        (sldConvertibleLayersDenoteAgreeUpTo areConvertible rowBound))

/-- Diagram-level convertibility: equal source arities and convertible layer lists. -/
def sldAreConvertibleDiagrams (leftDiagram rightDiagram : SldDiagram) : Prop :=
  leftDiagram.sourceArity = rightDiagram.sourceArity
    ∧ SldAreConvertibleLayers leftDiagram.sourceArity leftDiagram.layers rightDiagram.layers

/-! ## Defensive fires (2a)/(2b): the r30 refuted pairs are one-row firings here -/

/-- DEFENSIVE FIRE (2a): the r30 refuted unit pair `(id1 | eta) ; mu ~ id1` — in the layer
carrier the right side is the EMPTY LIST and the conversion is ONE row instance at zero pad
and empty suffix. -/
theorem sldRefutedUnitPairIsConvertible :
    SldAreConvertibleLayers 1 sldAddRightUnitLeftWindow [] := by
  have rowInstance := SldAreConvertibleLayers.fromAddRightUnitRow 0 0 []
  rw [sldPadWindowZeroIsSelf sldAddRightUnitLeftWindow,
    sldAppendLayersNilRightIsSelf sldAddRightUnitLeftWindow] at rowInstance
  exact rowInstance

/-- The mirror unit pair `(eta | id1) ; mu ~ id1`. -/
theorem sldMirrorUnitPairIsConvertible :
    SldAreConvertibleLayers 1 sldAddLeftUnitLeftWindow [] := by
  have rowInstance := SldAreConvertibleLayers.fromAddLeftUnitRow 0 0 []
  rw [sldPadWindowZeroIsSelf sldAddLeftUnitLeftWindow,
    sldAppendLayersNilRightIsSelf sldAddLeftUnitLeftWindow] at rowInstance
  exact rowInstance

/-- DEFENSIVE FIRE (2b): the r30 refuted associativity pair, one row instance. -/
theorem sldRefutedAssociativityPairIsConvertible :
    SldAreConvertibleLayers 3 sldAddAssociativityLeftWindow
      sldAddAssociativityRightWindow := by
  have rowInstance := SldAreConvertibleLayers.fromAddAssociativityRow 0 0 []
  rw [sldPadWindowZeroIsSelf sldAddAssociativityLeftWindow,
    sldPadWindowZeroIsSelf sldAddAssociativityRightWindow,
    sldAppendLayersNilRightIsSelf sldAddAssociativityLeftWindow,
    sldAppendLayersNilRightIsSelf sldAddAssociativityRightWindow] at rowInstance
  exact rowInstance

/-- The closed-loop fire: `eta ; epsilon ~ id0` — the r30 gated-absorber content, now a row
whose right side is LITERALLY NOTHING. -/
theorem sldClosedLoopDiesIntoEmptySyntax :
    SldAreConvertibleLayers 0 sldDiscardAfterZeroLeftWindow [] := by
  have rowInstance := SldAreConvertibleLayers.fromDiscardAfterZeroRow 0 0 []
  rw [sldPadWindowZeroIsSelf sldDiscardAfterZeroLeftWindow,
    sldAppendLayersNilRightIsSelf sldDiscardAfterZeroLeftWindow] at rowInstance
  exact rowInstance

/-- Consumption: soundness on the unit fire — its two sides denote the identity 1x1 matrix. -/
theorem sldUnitFireDenotesIdentity :
    doEntriesAgreeUpTo 1 1 (sldLayersDenote sldAddRightUnitLeftWindow)
      (sldLayersDenote []) = true :=
  sldConvertibleLayersDenoteAgreeUpTo sldRefutedUnitPairIsConvertible 1

/-! ## The embedding of the binary syntax -/

/-- Flatten the r1 binary-tensor syntax into the strict-layer carrier: identities to the
EMPTY list, sequential composition to append, parallel tensor to the zip, generators to
one-cell one-layer diagrams. -/
def sldOfWireDiagram : {sourceArity targetArity : Nat} ->
    WireDiagram sourceArity targetArity -> SldDiagram
  | _, _, WireDiagram.identityWires strandCount => sldIdentityDiagram strandCount
  | _, _, WireDiagram.composeSequential firstStage secondStage =>
      sldComposeSequential (sldOfWireDiagram firstStage) (sldOfWireDiagram secondStage)
  | _, _, WireDiagram.tensorParallel topDiagram bottomDiagram =>
      sldTensorParallel (sldOfWireDiagram topDiagram) (sldOfWireDiagram bottomDiagram)
  | _, _, WireDiagram.addGen => { sourceArity := 2, layers := [[SldCell.generatorMu]] }
  | _, _, WireDiagram.zeroGen => { sourceArity := 0, layers := [[SldCell.generatorEta]] }
  | _, _, WireDiagram.copyGen => { sourceArity := 1, layers := [[SldCell.generatorDelta]] }
  | _, _, WireDiagram.discardGen =>
      { sourceArity := 1, layers := [[SldCell.generatorEpsilon]] }
  | _, _, WireDiagram.swapGen => { sourceArity := 2, layers := [[SldCell.crossing]] }

/-- The embedding preserves the source arity. -/
theorem sldOfWireDiagramSourceArity : {sourceArity targetArity : Nat} ->
    (diagram : WireDiagram sourceArity targetArity) ->
    (sldOfWireDiagram diagram).sourceArity = sourceArity
  | _, _, WireDiagram.identityWires _ => rfl
  | _, _, WireDiagram.composeSequential firstStage _ => sldOfWireDiagramSourceArity firstStage
  | _, _, WireDiagram.tensorParallel topDiagram bottomDiagram => by
      show (sldOfWireDiagram topDiagram).sourceArity
          + (sldOfWireDiagram bottomDiagram).sourceArity = _
      rw [sldOfWireDiagramSourceArity topDiagram, sldOfWireDiagramSourceArity bottomDiagram]
  | _, _, WireDiagram.addGen => rfl
  | _, _, WireDiagram.zeroGen => rfl
  | _, _, WireDiagram.copyGen => rfl
  | _, _, WireDiagram.discardGen => rfl
  | _, _, WireDiagram.swapGen => rfl

/-- The embedding preserves the target arity (mutually feeding the boundary-meet condition
of composites). -/
theorem sldOfWireDiagramTargetArity : {sourceArity targetArity : Nat} ->
    (diagram : WireDiagram sourceArity targetArity) ->
    sldTargetArity (sldOfWireDiagram diagram) = targetArity
  | _, _, WireDiagram.identityWires _ => rfl
  | _, _, WireDiagram.composeSequential firstStage secondStage => by
      have doBoundariesMeet : (sldOfWireDiagram secondStage).sourceArity
          = sldTargetArity (sldOfWireDiagram firstStage) := by
        rw [sldOfWireDiagramSourceArity secondStage, sldOfWireDiagramTargetArity firstStage]
      show sldTargetArity
        (sldComposeSequential (sldOfWireDiagram firstStage) (sldOfWireDiagram secondStage))
          = _
      rw [sldComposeSequentialTargetArity (sldOfWireDiagram firstStage)
        (sldOfWireDiagram secondStage) doBoundariesMeet]
      exact sldOfWireDiagramTargetArity secondStage
  | _, _, WireDiagram.tensorParallel topDiagram bottomDiagram => by
      show sldTargetArity
        (sldTensorParallel (sldOfWireDiagram topDiagram) (sldOfWireDiagram bottomDiagram)) = _
      rw [sldTensorParallelTargetArity (sldOfWireDiagram topDiagram)
        (sldOfWireDiagram bottomDiagram),
        sldOfWireDiagramTargetArity topDiagram, sldOfWireDiagramTargetArity bottomDiagram]
  | _, _, WireDiagram.addGen => rfl
  | _, _, WireDiagram.zeroGen => rfl
  | _, _, WireDiagram.copyGen => rfl
  | _, _, WireDiagram.discardGen => rfl
  | _, _, WireDiagram.swapGen => rfl

/-- The embedding always produces a composable diagram. -/
theorem sldOfWireDiagramIsComposable : {sourceArity targetArity : Nat} ->
    (diagram : WireDiagram sourceArity targetArity) ->
    sldIsComposable (sldOfWireDiagram diagram) = true
  | _, _, WireDiagram.identityWires _ => rfl
  | _, _, WireDiagram.composeSequential firstStage secondStage => by
      refine sldComposeSequentialIsComposable (sldOfWireDiagram firstStage)
        (sldOfWireDiagram secondStage) (sldOfWireDiagramIsComposable firstStage)
        (sldOfWireDiagramIsComposable secondStage) ?_
      rw [sldOfWireDiagramSourceArity secondStage, sldOfWireDiagramTargetArity firstStage]
  | _, _, WireDiagram.tensorParallel topDiagram bottomDiagram =>
      sldTensorParallelIsComposable (sldOfWireDiagram topDiagram)
        (sldOfWireDiagram bottomDiagram) (sldOfWireDiagramIsComposable topDiagram)
        (sldOfWireDiagramIsComposable bottomDiagram)
  | _, _, WireDiagram.addGen => rfl
  | _, _, WireDiagram.zeroGen => rfl
  | _, _, WireDiagram.copyGen => rfl
  | _, _, WireDiagram.discardGen => rfl
  | _, _, WireDiagram.swapGen => rfl

/-- THE BRIDGE, pointwise: on the boundary rectangle the layer semantics of the embedding
agrees with the r1 matrix semantics. -/
theorem sldOfWireDiagramDenoteEntry : {sourceArity targetArity : Nat} ->
    (diagram : WireDiagram sourceArity targetArity) ->
    (rowIndex colIndex : Nat) -> rowIndex < targetArity -> colIndex < sourceArity ->
    sldDenote (sldOfWireDiagram diagram) rowIndex colIndex
      = denoteEntries diagram rowIndex colIndex
  | _, _, WireDiagram.identityWires _, _, _, _, _ => rfl
  | _, _, @WireDiagram.composeSequential sourceArity middleArity targetArity
      firstStage secondStage, rowIndex, colIndex, isRowInside, isColInside => by
      have isColInsideEmbedded : colIndex < (sldOfWireDiagram firstStage).sourceArity := by
        rw [sldOfWireDiagramSourceArity firstStage]
        exact isColInside
      show sldLayersDenote
          (sldAppendLayers (sldOfWireDiagram firstStage).layers
            (sldOfWireDiagram secondStage).layers) rowIndex colIndex
        = composeEntries middleArity (denoteEntries secondStage) (denoteEntries firstStage)
            rowIndex colIndex
      refine Eq.trans (sldDenoteOfAppendAsProductEntry (sldOfWireDiagram firstStage).layers
        (sldOfWireDiagram firstStage).sourceArity (sldOfWireDiagram secondStage).layers
        rowIndex colIndex isColInsideEmbedded) ?_
      have doesFirstReach : sldLayersTargetArityFrom (sldOfWireDiagram firstStage).sourceArity
          (sldOfWireDiagram firstStage).layers = middleArity :=
        sldOfWireDiagramTargetArity firstStage
      rw [doesFirstReach]
      exact sldProductRespectsEntryAgreement middleArity
        (sldLayersDenote (sldOfWireDiagram secondStage).layers) (denoteEntries secondStage)
        (sldLayersDenote (sldOfWireDiagram firstStage).layers) (denoteEntries firstStage)
        rowIndex colIndex
        (fun middleIndex isMiddleInside =>
          sldOfWireDiagramDenoteEntry secondStage rowIndex middleIndex isRowInside
            isMiddleInside)
        (fun middleIndex isMiddleInside =>
          sldOfWireDiagramDenoteEntry firstStage middleIndex colIndex isMiddleInside
            isColInside)
  | _, _, @WireDiagram.tensorParallel topSourceArity topTargetArity
      bottomSourceArity bottomTargetArity topDiagram bottomDiagram,
      rowIndex, colIndex, isRowInside, isColInside => by
      show sldLayersDenote
          (sldZipLayersWithPads (sldTargetArity (sldOfWireDiagram topDiagram))
            (sldTargetArity (sldOfWireDiagram bottomDiagram))
            (sldOfWireDiagram topDiagram).layers (sldOfWireDiagram bottomDiagram).layers)
          rowIndex colIndex
        = directSumEntries topTargetArity topSourceArity (denoteEntries topDiagram)
            (denoteEntries bottomDiagram) rowIndex colIndex
      refine Eq.trans (sldDenoteOfZipAsDirectSumEntry
        (sldTargetArity (sldOfWireDiagram topDiagram))
        (sldTargetArity (sldOfWireDiagram bottomDiagram))
        (sldOfWireDiagram topDiagram).layers (sldOfWireDiagram bottomDiagram).layers
        (sldOfWireDiagram topDiagram).sourceArity
        (sldOfWireDiagram bottomDiagram).sourceArity
        (sldOfWireDiagramIsComposable topDiagram)
        (sldOfWireDiagramIsComposable bottomDiagram) rfl rfl rowIndex colIndex ?_ ?_) ?_
      · rw [sldOfWireDiagramTargetArity topDiagram, sldOfWireDiagramTargetArity bottomDiagram]
        exact isRowInside
      · rw [sldOfWireDiagramSourceArity topDiagram, sldOfWireDiagramSourceArity bottomDiagram]
        exact isColInside
      · rw [sldOfWireDiagramTargetArity topDiagram, sldOfWireDiagramSourceArity topDiagram]
        refine sldDirectSumRespectsEntryAgreement topTargetArity topSourceArity
          (sldLayersDenote (sldOfWireDiagram topDiagram).layers) (denoteEntries topDiagram)
          (sldLayersDenote (sldOfWireDiagram bottomDiagram).layers)
          (denoteEntries bottomDiagram) rowIndex colIndex
          (fun isRowInTop isColInTop =>
            sldOfWireDiagramDenoteEntry topDiagram rowIndex colIndex isRowInTop isColInTop) ?_
        intro rowOffset colOffset doesRowSplit doesColSplit
        refine sldOfWireDiagramDenoteEntry bottomDiagram rowOffset colOffset ?_ ?_
        · rw [doesRowSplit] at isRowInside
          exact ltOfAddLtAddLeft topTargetArity isRowInside
        · rw [doesColSplit] at isColInside
          exact ltOfAddLtAddLeft topSourceArity isColInside
  | _, _, WireDiagram.addGen, rowIndex, colIndex, isRowInside, isColInside =>
      pointwiseOfAgreeUpTo 1 2 (sldLayersDenote [[SldCell.generatorMu]]) addGenEntries rfl
        rowIndex colIndex isRowInside isColInside
  | _, _, WireDiagram.zeroGen, rowIndex, colIndex, isRowInside, isColInside =>
      pointwiseOfAgreeUpTo 1 0 (sldLayersDenote [[SldCell.generatorEta]]) zeroGenEntries rfl
        rowIndex colIndex isRowInside isColInside
  | _, _, WireDiagram.copyGen, rowIndex, colIndex, isRowInside, isColInside =>
      pointwiseOfAgreeUpTo 2 1 (sldLayersDenote [[SldCell.generatorDelta]]) copyGenEntries rfl
        rowIndex colIndex isRowInside isColInside
  | _, _, WireDiagram.discardGen, rowIndex, colIndex, isRowInside, isColInside =>
      pointwiseOfAgreeUpTo 0 1 (sldLayersDenote [[SldCell.generatorEpsilon]])
        discardGenEntries rfl rowIndex colIndex isRowInside isColInside
  | _, _, WireDiagram.swapGen, rowIndex, colIndex, isRowInside, isColInside =>
      pointwiseOfAgreeUpTo 2 2 (sldLayersDenote [[SldCell.crossing]]) swapGenEntries rfl
        rowIndex colIndex isRowInside isColInside

/-- THE BRIDGE, Bool form: the embedding preserves the Mat(N) denotation on the full
rectangle. -/
theorem sldOfWireDiagramDenoteAgrees {sourceArity targetArity : Nat}
    (diagram : WireDiagram sourceArity targetArity) :
    doEntriesAgreeUpTo targetArity sourceArity (sldDenote (sldOfWireDiagram diagram))
      (denoteEntries diagram) = true :=
  agreeUpToOfPointwise targetArity sourceArity (sldDenote (sldOfWireDiagram diagram))
    (denoteEntries diagram)
    (fun rowIndex colIndex isRowInside isColInside =>
      sldOfWireDiagramDenoteEntry diagram rowIndex colIndex isRowInside isColInside)

/-! ## THE EX-SEPARATOR DISSOLVES (defensive fire 1, embedding form) -/

/-- THE DISSOLUTION FIRE: the embedding maps the r3 separator `id0 | delta` and bare `delta`
to the SAME strict-layer diagram — kernel `rfl`.  The equal-matrix NON-convertible pair of
the binary syntax is not even a PAIR here. -/
theorem sldEmbeddingDissolvesTheSeparator :
    sldOfWireDiagram leftPaddedCopyDiagram = sldOfWireDiagram WireDiagram.copyGen := rfl

/-- The full record: the r3 anomaly-parity invariant SEPARATED the two sides (odd vs even);
the embedding maps them to one term.  All three components kernel `rfl`. -/
theorem sldEmbeddingCollapsesAnomalyParity :
    hasOddAnomalousBoundaryCount leftPaddedCopyDiagram = true
      ∧ hasOddAnomalousBoundaryCount WireDiagram.copyGen = false
      ∧ sldOfWireDiagram leftPaddedCopyDiagram = sldOfWireDiagram WireDiagram.copyGen :=
  ⟨rfl, rfl, rfl⟩

/-- The other statable pad direction dissolves too. -/
theorem sldEmbeddingDissolvesBottomPadding :
    sldOfWireDiagram (WireDiagram.tensorParallel WireDiagram.copyGen
        (WireDiagram.identityWires 0))
      = sldOfWireDiagram WireDiagram.copyGen := rfl

/-! ## Derived congruence plumbing (toward the convertibility transport) -/

/-- Congruence under a whole leading layer list. -/
theorem sldConvUnderPrefixList :
    (prefixLayers : List SldLayer) -> (outerBoundary : Nat) ->
    (tailLeft tailRight : List SldLayer) ->
    SldAreConvertibleLayers (sldLayersTargetArityFrom outerBoundary prefixLayers)
      tailLeft tailRight ->
    SldAreConvertibleLayers outerBoundary (sldAppendLayers prefixLayers tailLeft)
      (sldAppendLayers prefixLayers tailRight)
  | [], _, _, _, innerConvertible => innerConvertible
  | contextLayer :: restLayers, outerBoundary, tailLeft, tailRight, innerConvertible =>
      SldAreConvertibleLayers.underLayerPrefix outerBoundary contextLayer
        (sldConvUnderPrefixList restLayers (sldLayerTargetArity contextLayer)
          tailLeft tailRight innerConvertible)

/-- Congruence under a common suffix — every leaf constructor already carries a suffix slot,
so appending distributes definitionally into it. -/
theorem sldConvAppendsSuffix {boundaryArity : Nat} {leftLayers rightLayers : List SldLayer}
    (areConvertible : SldAreConvertibleLayers boundaryArity leftLayers rightLayers)
    (extraLayers : List SldLayer) :
    SldAreConvertibleLayers boundaryArity (sldAppendLayers leftLayers extraLayers)
      (sldAppendLayers rightLayers extraLayers) := by
  induction areConvertible with
  | fromReflexivity innerBoundary layers =>
      exact .fromReflexivity innerBoundary (sldAppendLayers layers extraLayers)
  | fromSymmetry _ flippedAppended => exact .fromSymmetry flippedAppended
  | fromTransitivity _ _ leftAppended rightAppended =>
      exact .fromTransitivity leftAppended rightAppended
  | underLayerPrefix innerBoundary contextLayer _ tailAppended =>
      exact .underLayerPrefix innerBoundary contextLayer tailAppended
  | layerSplitTopActsFirst topCells bottomCells suffixLayers =>
      exact .layerSplitTopActsFirst topCells bottomCells
        (sldAppendLayers suffixLayers extraLayers)
  | layerSplitBottomActsFirst topCells bottomCells suffixLayers =>
      exact .layerSplitBottomActsFirst topCells bottomCells
        (sldAppendLayers suffixLayers extraLayers)
  | fromAddAssociativityRow padAboveCount padBelowCount suffixLayers =>
      exact .fromAddAssociativityRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromAddLeftUnitRow padAboveCount padBelowCount suffixLayers =>
      exact .fromAddLeftUnitRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromAddRightUnitRow padAboveCount padBelowCount suffixLayers =>
      exact .fromAddRightUnitRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromAddCommutativityRow padAboveCount padBelowCount suffixLayers =>
      exact .fromAddCommutativityRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromCopyCoassociativityRow padAboveCount padBelowCount suffixLayers =>
      exact .fromCopyCoassociativityRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromCopyLeftCounitRow padAboveCount padBelowCount suffixLayers =>
      exact .fromCopyLeftCounitRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromCopyRightCounitRow padAboveCount padBelowCount suffixLayers =>
      exact .fromCopyRightCounitRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromCopyCocommutativityRow padAboveCount padBelowCount suffixLayers =>
      exact .fromCopyCocommutativityRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromBimonoidSquareRow padAboveCount padBelowCount suffixLayers =>
      exact .fromBimonoidSquareRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromCopyAfterZeroRow padAboveCount padBelowCount suffixLayers =>
      exact .fromCopyAfterZeroRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromDiscardAfterAddRow padAboveCount padBelowCount suffixLayers =>
      exact .fromDiscardAfterAddRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromDiscardAfterZeroRow padAboveCount padBelowCount suffixLayers =>
      exact .fromDiscardAfterZeroRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromSwapInvolutionRow padAboveCount padBelowCount suffixLayers =>
      exact .fromSwapInvolutionRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromSwapYangBaxterRow padAboveCount padBelowCount suffixLayers =>
      exact .fromSwapYangBaxterRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromSwapPastAddRow padAboveCount padBelowCount suffixLayers =>
      exact .fromSwapPastAddRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromSwapPastZeroRow padAboveCount padBelowCount suffixLayers =>
      exact .fromSwapPastZeroRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromCopyPastSwapRow padAboveCount padBelowCount suffixLayers =>
      exact .fromCopyPastSwapRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)
  | fromDiscardPastSwapRow padAboveCount padBelowCount suffixLayers =>
      exact .fromDiscardPastSwapRow padAboveCount padBelowCount
        (sldAppendLayers suffixLayers extraLayers)

/-! ### Pad distribution laws (list level) -/

/-- Extending a padded layer below merges the wire counts. -/
theorem sldPadLayerBelowExtension (padAboveCount padBelowCount extraCount : Nat)
    (windowLayer : SldLayer) :
    sldAppendCells (sldPadLayer padAboveCount padBelowCount windowLayer)
        (sldWireLayerOfArity extraCount)
      = sldPadLayer padAboveCount (padBelowCount + extraCount) windowLayer := by
  show sldAppendCells (sldAppendCells (sldWireLayerOfArity padAboveCount)
      (sldAppendCells windowLayer (sldWireLayerOfArity padBelowCount)))
      (sldWireLayerOfArity extraCount)
    = sldAppendCells (sldWireLayerOfArity padAboveCount)
        (sldAppendCells windowLayer (sldWireLayerOfArity (padBelowCount + extraCount)))
  rw [sldAppendCellsAssoc, sldAppendCellsAssoc, sldWireLayerSplitsAtCount]

/-- Extending a padded layer above merges the wire counts. -/
theorem sldPadLayerAboveExtension (extraCount padAboveCount padBelowCount : Nat)
    (windowLayer : SldLayer) :
    sldAppendCells (sldWireLayerOfArity extraCount)
        (sldPadLayer padAboveCount padBelowCount windowLayer)
      = sldPadLayer (extraCount + padAboveCount) padBelowCount windowLayer := by
  show sldAppendCells (sldWireLayerOfArity extraCount)
      (sldAppendCells (sldWireLayerOfArity padAboveCount)
        (sldAppendCells windowLayer (sldWireLayerOfArity padBelowCount)))
    = sldAppendCells (sldWireLayerOfArity (extraCount + padAboveCount))
        (sldAppendCells windowLayer (sldWireLayerOfArity padBelowCount))
  rw [(sldAppendCellsAssoc (sldWireLayerOfArity extraCount)
      (sldWireLayerOfArity padAboveCount)
      (sldAppendCells windowLayer (sldWireLayerOfArity padBelowCount))).symm,
    sldWireLayerSplitsAtCount]

/-- Below-padding distributes over layer-list append. -/
theorem sldPadLayersBelowOfAppend (padCount : Nat) :
    (firstLayers secondLayers : List SldLayer) ->
    sldPadLayersBelow padCount (sldAppendLayers firstLayers secondLayers)
      = sldAppendLayers (sldPadLayersBelow padCount firstLayers)
          (sldPadLayersBelow padCount secondLayers)
  | [], _ => rfl
  | headLayer :: tailLayers, secondLayers =>
      congrArg (fun restLayers =>
        sldAppendCells headLayer (sldWireLayerOfArity padCount) :: restLayers)
        (sldPadLayersBelowOfAppend padCount tailLayers secondLayers)

/-- Above-padding distributes over layer-list append. -/
theorem sldPadLayersAboveOfAppend (padCount : Nat) :
    (firstLayers secondLayers : List SldLayer) ->
    sldPadLayersAbove padCount (sldAppendLayers firstLayers secondLayers)
      = sldAppendLayers (sldPadLayersAbove padCount firstLayers)
          (sldPadLayersAbove padCount secondLayers)
  | [], _ => rfl
  | headLayer :: tailLayers, secondLayers =>
      congrArg (fun restLayers =>
        sldAppendCells (sldWireLayerOfArity padCount) headLayer :: restLayers)
        (sldPadLayersAboveOfAppend padCount tailLayers secondLayers)

/-- Below-padding a padded window widens the below pad. -/
theorem sldPadLayersBelowOfPadWindow (padAboveCount padBelowCount extraCount : Nat) :
    (windowLayers : List SldLayer) ->
    sldPadLayersBelow extraCount (sldPadWindow padAboveCount padBelowCount windowLayers)
      = sldPadWindow padAboveCount (padBelowCount + extraCount) windowLayers
  | [] => rfl
  | headLayer :: tailLayers => by
      show sldAppendCells (sldPadLayer padAboveCount padBelowCount headLayer)
          (sldWireLayerOfArity extraCount)
          :: sldPadLayersBelow extraCount
              (sldPadWindow padAboveCount padBelowCount tailLayers)
        = sldPadLayer padAboveCount (padBelowCount + extraCount) headLayer
          :: sldPadWindow padAboveCount (padBelowCount + extraCount) tailLayers
      rw [sldPadLayerBelowExtension,
        sldPadLayersBelowOfPadWindow padAboveCount padBelowCount extraCount tailLayers]

/-- Above-padding a padded window widens the above pad. -/
theorem sldPadLayersAboveOfPadWindow (extraCount padAboveCount padBelowCount : Nat) :
    (windowLayers : List SldLayer) ->
    sldPadLayersAbove extraCount (sldPadWindow padAboveCount padBelowCount windowLayers)
      = sldPadWindow (extraCount + padAboveCount) padBelowCount windowLayers
  | [] => rfl
  | headLayer :: tailLayers => by
      show sldAppendCells (sldWireLayerOfArity extraCount)
          (sldPadLayer padAboveCount padBelowCount headLayer)
          :: sldPadLayersAbove extraCount
              (sldPadWindow padAboveCount padBelowCount tailLayers)
        = sldPadLayer (extraCount + padAboveCount) padBelowCount headLayer
          :: sldPadWindow (extraCount + padAboveCount) padBelowCount tailLayers
      rw [sldPadLayerAboveExtension,
        sldPadLayersAboveOfPadWindow extraCount padAboveCount padBelowCount tailLayers]

/-- Row-index reassociation for the below-pad congruence. -/
theorem sldPadIndexShuffleBelow (padAboveCount windowArity padBelowCount padCount : Nat) :
    padAboveCount + (windowArity + (padBelowCount + padCount))
      = (padAboveCount + (windowArity + padBelowCount)) + padCount := by
  rw [Nat.add_assoc padAboveCount (windowArity + padBelowCount) padCount,
    Nat.add_assoc windowArity padBelowCount padCount]

/-- Row-index reassociation for the above-pad congruence. -/
theorem sldPadIndexShuffleAbove (padCount padAboveCount tailSum : Nat) :
    (padCount + padAboveCount) + tailSum = padCount + (padAboveCount + tailSum) :=
  Nat.add_assoc padCount padAboveCount tailSum


/-- ONE-SIDED PAD CONGRUENCE, below: a conversion stays a conversion when every layer gains a
wire pad below — induction over the derivation (rows widen their below pad, splits re-slice). -/
theorem sldConvPadsBelow {boundaryArity : Nat} {leftLayers rightLayers : List SldLayer}
    (areConvertible : SldAreConvertibleLayers boundaryArity leftLayers rightLayers)
    (padCount : Nat) :
    SldAreConvertibleLayers (boundaryArity + padCount)
      (sldPadLayersBelow padCount leftLayers) (sldPadLayersBelow padCount rightLayers) := by
  induction areConvertible with
  | fromReflexivity innerBoundary layers =>
      exact .fromReflexivity (innerBoundary + padCount) (sldPadLayersBelow padCount layers)
  | fromSymmetry _ flippedPadded => exact .fromSymmetry flippedPadded
  | fromTransitivity _ _ leftPadded rightPadded =>
      exact .fromTransitivity leftPadded rightPadded
  | underLayerPrefix innerBoundary contextLayer _ tailPadded =>
      refine .underLayerPrefix (innerBoundary + padCount)
        (sldAppendCells contextLayer (sldWireLayerOfArity padCount)) ?_
      rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
      exact tailPadded
  | layerSplitTopActsFirst topCells bottomCells suffixLayers =>
      have coreSplit := SldAreConvertibleLayers.layerSplitTopActsFirst topCells
        (sldAppendCells bottomCells (sldWireLayerOfArity padCount))
        (sldPadLayersBelow padCount suffixLayers)
      rw [(sldAppendCellsAssoc topCells bottomCells (sldWireLayerOfArity padCount)).symm,
        (sldAppendCellsAssoc (sldWireLayerOfArity (sldLayerTargetArity topCells)) bottomCells
          (sldWireLayerOfArity padCount)).symm,
        sldAppendCellsSourceArity (sldAppendCells topCells bottomCells)
          (sldWireLayerOfArity padCount),
        sldAppendCellsSourceArity bottomCells (sldWireLayerOfArity padCount),
        sldWireLayerSourceArity,
        (sldWireLayerSplitsAtCount (sldLayerSourceArity bottomCells) padCount).symm,
        (sldAppendCellsAssoc topCells
          (sldWireLayerOfArity (sldLayerSourceArity bottomCells))
          (sldWireLayerOfArity padCount)).symm] at coreSplit
      exact coreSplit
  | layerSplitBottomActsFirst topCells bottomCells suffixLayers =>
      have coreSplit := SldAreConvertibleLayers.layerSplitBottomActsFirst topCells
        (sldAppendCells bottomCells (sldWireLayerOfArity padCount))
        (sldPadLayersBelow padCount suffixLayers)
      rw [(sldAppendCellsAssoc topCells bottomCells (sldWireLayerOfArity padCount)).symm,
        (sldAppendCellsAssoc (sldWireLayerOfArity (sldLayerSourceArity topCells)) bottomCells
          (sldWireLayerOfArity padCount)).symm,
        sldAppendCellsSourceArity (sldAppendCells topCells bottomCells)
          (sldWireLayerOfArity padCount),
        sldAppendCellsTargetArity bottomCells (sldWireLayerOfArity padCount),
        sldWireLayerSourceArity, sldWireLayerTargetArity,
        (sldWireLayerSplitsAtCount (sldLayerTargetArity bottomCells) padCount).symm,
        (sldAppendCellsAssoc topCells
          (sldWireLayerOfArity (sldLayerTargetArity bottomCells))
          (sldWireLayerOfArity padCount)).symm] at coreSplit
      exact coreSplit
  | fromAddAssociativityRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromAddAssociativityRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 3 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldAddAssociativityLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldAddAssociativityRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddAssociativityLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddAssociativityRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromAddLeftUnitRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromAddLeftUnitRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 1 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldAddLeftUnitLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldAddLeftUnitRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddLeftUnitLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddLeftUnitRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromAddRightUnitRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromAddRightUnitRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 1 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldAddRightUnitLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldAddRightUnitRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddRightUnitLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddRightUnitRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromAddCommutativityRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromAddCommutativityRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 2 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldAddCommutativityLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldAddCommutativityRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddCommutativityLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddCommutativityRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromCopyCoassociativityRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromCopyCoassociativityRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 1 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldCopyCoassociativityLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldCopyCoassociativityRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyCoassociativityLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyCoassociativityRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromCopyLeftCounitRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromCopyLeftCounitRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 1 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldCopyLeftCounitLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldCopyLeftCounitRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyLeftCounitLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyLeftCounitRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromCopyRightCounitRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromCopyRightCounitRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 1 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldCopyRightCounitLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldCopyRightCounitRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyRightCounitLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyRightCounitRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromCopyCocommutativityRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromCopyCocommutativityRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 1 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldCopyCocommutativityLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldCopyCocommutativityRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyCocommutativityLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyCocommutativityRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromBimonoidSquareRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromBimonoidSquareRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 2 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldBimonoidSquareLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldBimonoidSquareRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldBimonoidSquareLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldBimonoidSquareRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromCopyAfterZeroRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromCopyAfterZeroRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 0 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldCopyAfterZeroLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldCopyAfterZeroRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyAfterZeroLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyAfterZeroRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromDiscardAfterAddRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromDiscardAfterAddRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 2 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldDiscardAfterAddLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldDiscardAfterAddRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldDiscardAfterAddLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldDiscardAfterAddRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromDiscardAfterZeroRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromDiscardAfterZeroRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 0 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldDiscardAfterZeroLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldDiscardAfterZeroRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldDiscardAfterZeroLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldDiscardAfterZeroRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromSwapInvolutionRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromSwapInvolutionRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 2 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldSwapInvolutionLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldSwapInvolutionRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapInvolutionLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapInvolutionRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromSwapYangBaxterRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromSwapYangBaxterRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 3 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldSwapYangBaxterLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldSwapYangBaxterRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapYangBaxterLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapYangBaxterRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromSwapPastAddRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromSwapPastAddRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 3 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldSwapPastAddLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldSwapPastAddRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapPastAddLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapPastAddRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromSwapPastZeroRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromSwapPastZeroRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 1 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldSwapPastZeroLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldSwapPastZeroRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapPastZeroLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapPastZeroRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromCopyPastSwapRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromCopyPastSwapRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 2 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldCopyPastSwapLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldCopyPastSwapRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyPastSwapLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyPastSwapRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromDiscardPastSwapRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromDiscardPastSwapRow padAboveCount
        (padBelowCount + padCount) (sldPadLayersBelow padCount suffixLayers)
      rw [sldPadIndexShuffleBelow padAboveCount 2 padBelowCount padCount,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldDiscardPastSwapLeftWindow).symm,
        (sldPadLayersBelowOfPadWindow padAboveCount padBelowCount padCount
          sldDiscardPastSwapRightWindow).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldDiscardPastSwapLeftWindow)
          suffixLayers).symm,
        (sldPadLayersBelowOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldDiscardPastSwapRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance

/-- ONE-SIDED PAD CONGRUENCE, above: a conversion stays a conversion when every layer gains a
wire pad above. -/
theorem sldConvPadsAbove {boundaryArity : Nat} {leftLayers rightLayers : List SldLayer}
    (areConvertible : SldAreConvertibleLayers boundaryArity leftLayers rightLayers)
    (padCount : Nat) :
    SldAreConvertibleLayers (padCount + boundaryArity)
      (sldPadLayersAbove padCount leftLayers) (sldPadLayersAbove padCount rightLayers) := by
  induction areConvertible with
  | fromReflexivity innerBoundary layers =>
      exact .fromReflexivity (padCount + innerBoundary) (sldPadLayersAbove padCount layers)
  | fromSymmetry _ flippedPadded => exact .fromSymmetry flippedPadded
  | fromTransitivity _ _ leftPadded rightPadded =>
      exact .fromTransitivity leftPadded rightPadded
  | underLayerPrefix innerBoundary contextLayer _ tailPadded =>
      refine .underLayerPrefix (padCount + innerBoundary)
        (sldAppendCells (sldWireLayerOfArity padCount) contextLayer) ?_
      rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
      exact tailPadded
  | layerSplitTopActsFirst topCells bottomCells suffixLayers =>
      have coreSplit := SldAreConvertibleLayers.layerSplitTopActsFirst
        (sldAppendCells (sldWireLayerOfArity padCount) topCells) bottomCells
        (sldPadLayersAbove padCount suffixLayers)
      rw [sldAppendCellsAssoc (sldWireLayerOfArity padCount) topCells bottomCells,
        sldAppendCellsAssoc (sldWireLayerOfArity padCount) topCells
          (sldWireLayerOfArity (sldLayerSourceArity bottomCells)),
        sldAppendCellsTargetArity (sldWireLayerOfArity padCount) topCells,
        sldWireLayerTargetArity,
        (sldWireLayerSplitsAtCount padCount (sldLayerTargetArity topCells)).symm,
        sldAppendCellsAssoc (sldWireLayerOfArity padCount)
          (sldWireLayerOfArity (sldLayerTargetArity topCells)) bottomCells,
        sldAppendCellsSourceArity (sldWireLayerOfArity padCount)
          (sldAppendCells topCells bottomCells),
        sldWireLayerSourceArity] at coreSplit
      exact coreSplit
  | layerSplitBottomActsFirst topCells bottomCells suffixLayers =>
      have coreSplit := SldAreConvertibleLayers.layerSplitBottomActsFirst
        (sldAppendCells (sldWireLayerOfArity padCount) topCells) bottomCells
        (sldPadLayersAbove padCount suffixLayers)
      rw [sldAppendCellsAssoc (sldWireLayerOfArity padCount) topCells bottomCells,
        sldAppendCellsSourceArity (sldWireLayerOfArity padCount) topCells,
        sldWireLayerSourceArity,
        (sldWireLayerSplitsAtCount padCount (sldLayerSourceArity topCells)).symm,
        sldAppendCellsAssoc (sldWireLayerOfArity padCount)
          (sldWireLayerOfArity (sldLayerSourceArity topCells)) bottomCells,
        sldAppendCellsAssoc (sldWireLayerOfArity padCount) topCells
          (sldWireLayerOfArity (sldLayerTargetArity bottomCells)),
        sldAppendCellsSourceArity (sldWireLayerOfArity padCount)
          (sldAppendCells topCells bottomCells),
        sldWireLayerSourceArity] at coreSplit
      exact coreSplit
  | fromAddAssociativityRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromAddAssociativityRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (3 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldAddAssociativityLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldAddAssociativityRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddAssociativityLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddAssociativityRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromAddLeftUnitRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromAddLeftUnitRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (1 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldAddLeftUnitLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldAddLeftUnitRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddLeftUnitLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddLeftUnitRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromAddRightUnitRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromAddRightUnitRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (1 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldAddRightUnitLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldAddRightUnitRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddRightUnitLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddRightUnitRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromAddCommutativityRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromAddCommutativityRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (2 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldAddCommutativityLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldAddCommutativityRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddCommutativityLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldAddCommutativityRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromCopyCoassociativityRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromCopyCoassociativityRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (1 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldCopyCoassociativityLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldCopyCoassociativityRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyCoassociativityLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyCoassociativityRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromCopyLeftCounitRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromCopyLeftCounitRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (1 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldCopyLeftCounitLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldCopyLeftCounitRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyLeftCounitLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyLeftCounitRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromCopyRightCounitRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromCopyRightCounitRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (1 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldCopyRightCounitLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldCopyRightCounitRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyRightCounitLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyRightCounitRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromCopyCocommutativityRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromCopyCocommutativityRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (1 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldCopyCocommutativityLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldCopyCocommutativityRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyCocommutativityLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyCocommutativityRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromBimonoidSquareRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromBimonoidSquareRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (2 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldBimonoidSquareLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldBimonoidSquareRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldBimonoidSquareLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldBimonoidSquareRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromCopyAfterZeroRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromCopyAfterZeroRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (0 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldCopyAfterZeroLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldCopyAfterZeroRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyAfterZeroLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyAfterZeroRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromDiscardAfterAddRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromDiscardAfterAddRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (2 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldDiscardAfterAddLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldDiscardAfterAddRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldDiscardAfterAddLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldDiscardAfterAddRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromDiscardAfterZeroRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromDiscardAfterZeroRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (0 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldDiscardAfterZeroLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldDiscardAfterZeroRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldDiscardAfterZeroLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldDiscardAfterZeroRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromSwapInvolutionRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromSwapInvolutionRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (2 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldSwapInvolutionLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldSwapInvolutionRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapInvolutionLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapInvolutionRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromSwapYangBaxterRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromSwapYangBaxterRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (3 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldSwapYangBaxterLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldSwapYangBaxterRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapYangBaxterLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapYangBaxterRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromSwapPastAddRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromSwapPastAddRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (3 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldSwapPastAddLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldSwapPastAddRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapPastAddLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapPastAddRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromSwapPastZeroRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromSwapPastZeroRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (1 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldSwapPastZeroLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldSwapPastZeroRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapPastZeroLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldSwapPastZeroRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromCopyPastSwapRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromCopyPastSwapRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (2 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldCopyPastSwapLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldCopyPastSwapRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyPastSwapLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldCopyPastSwapRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance
  | fromDiscardPastSwapRow padAboveCount padBelowCount suffixLayers =>
      have rowInstance := SldAreConvertibleLayers.fromDiscardPastSwapRow
        (padCount + padAboveCount) padBelowCount (sldPadLayersAbove padCount suffixLayers)
      rw [sldPadIndexShuffleAbove padCount padAboveCount (2 + padBelowCount),
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldDiscardPastSwapLeftWindow).symm,
        (sldPadLayersAboveOfPadWindow padCount padAboveCount padBelowCount
          sldDiscardPastSwapRightWindow).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldDiscardPastSwapLeftWindow)
          suffixLayers).symm,
        (sldPadLayersAboveOfAppend padCount
          (sldPadWindow padAboveCount padBelowCount sldDiscardPastSwapRightWindow)
          suffixLayers).symm] at rowInstance
      exact rowInstance

/-! ### The slide family: layers and blocks commute past disjoint strand ranges -/

/-- A top-strand layer slides down past a bottom-strand block (induction on the block; each
step is one derived exchange). -/
theorem sldUpperLayerSlidesDownPastBlock (slidingLayer : SldLayer) :
    (blockLayers : List SldLayer) -> (blockBoundary : Nat) ->
    sldLayersAreComposableFrom blockBoundary blockLayers = true ->
    (suffixLayers : List SldLayer) ->
    SldAreConvertibleLayers (sldLayerSourceArity slidingLayer + blockBoundary)
      (sldAppendCells slidingLayer (sldWireLayerOfArity blockBoundary)
        :: sldAppendLayers (sldPadLayersAbove (sldLayerTargetArity slidingLayer) blockLayers)
            suffixLayers)
      (sldAppendLayers (sldPadLayersAbove (sldLayerSourceArity slidingLayer) blockLayers)
        (sldAppendCells slidingLayer
            (sldWireLayerOfArity (sldLayersTargetArityFrom blockBoundary blockLayers))
          :: suffixLayers))
  | [], _, _, _ => SldAreConvertibleLayers.fromReflexivity _ _
  | blockHead :: blockTail, blockBoundary, isChainComposable, suffixLayers => by
      have doesHeadMatch : sldLayerSourceArity blockHead = blockBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isChainComposable)
      have doesTailCompose := rightIsTrueOfAndTrue isChainComposable
      have exchangeStep := sldDisjointLayersExchange slidingLayer blockHead
        (sldAppendLayers
          (sldPadLayersAbove (sldLayerTargetArity slidingLayer) blockTail) suffixLayers)
      rw [sldAppendCellsSourceArity slidingLayer blockHead, doesHeadMatch] at exchangeStep
      refine SldAreConvertibleLayers.fromTransitivity exchangeStep ?_
      refine SldAreConvertibleLayers.underLayerPrefix
        (sldLayerSourceArity slidingLayer + blockBoundary)
        (sldAppendCells (sldWireLayerOfArity (sldLayerSourceArity slidingLayer)) blockHead) ?_
      rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
      exact sldUpperLayerSlidesDownPastBlock slidingLayer blockTail
        (sldLayerTargetArity blockHead) doesTailCompose suffixLayers

/-- A bottom-strand layer slides down past a top-strand block. -/
theorem sldLowerLayerSlidesDownPastBlock (slidingLayer : SldLayer) :
    (blockLayers : List SldLayer) -> (blockBoundary : Nat) ->
    sldLayersAreComposableFrom blockBoundary blockLayers = true ->
    (suffixLayers : List SldLayer) ->
    SldAreConvertibleLayers (blockBoundary + sldLayerSourceArity slidingLayer)
      (sldAppendCells (sldWireLayerOfArity blockBoundary) slidingLayer
        :: sldAppendLayers (sldPadLayersBelow (sldLayerTargetArity slidingLayer) blockLayers)
            suffixLayers)
      (sldAppendLayers (sldPadLayersBelow (sldLayerSourceArity slidingLayer) blockLayers)
        (sldAppendCells
            (sldWireLayerOfArity (sldLayersTargetArityFrom blockBoundary blockLayers))
            slidingLayer
          :: suffixLayers))
  | [], _, _, _ => SldAreConvertibleLayers.fromReflexivity _ _
  | blockHead :: blockTail, blockBoundary, isChainComposable, suffixLayers => by
      have doesHeadMatch : sldLayerSourceArity blockHead = blockBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isChainComposable)
      have doesTailCompose := rightIsTrueOfAndTrue isChainComposable
      have exchangeStep := sldDisjointLayersExchange blockHead slidingLayer
        (sldAppendLayers
          (sldPadLayersBelow (sldLayerTargetArity slidingLayer) blockTail) suffixLayers)
      rw [sldAppendCellsSourceArity blockHead slidingLayer, doesHeadMatch] at exchangeStep
      refine SldAreConvertibleLayers.fromTransitivity
        (SldAreConvertibleLayers.fromSymmetry exchangeStep) ?_
      refine SldAreConvertibleLayers.underLayerPrefix
        (blockBoundary + sldLayerSourceArity slidingLayer)
        (sldAppendCells blockHead (sldWireLayerOfArity (sldLayerSourceArity slidingLayer))) ?_
      rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
      exact sldLowerLayerSlidesDownPastBlock slidingLayer blockTail
        (sldLayerTargetArity blockHead) doesTailCompose suffixLayers

/-- A whole top-strand block slides down past a whole bottom-strand block — the Godement
interchange of two vertically-stacked phases, as a conversion. -/
theorem sldBlockSlidesDownPastBlock :
    (topBlockLayers : List SldLayer) -> (topBoundary : Nat) ->
    sldLayersAreComposableFrom topBoundary topBlockLayers = true ->
    (bottomBlockLayers : List SldLayer) -> (bottomBoundary : Nat) ->
    sldLayersAreComposableFrom bottomBoundary bottomBlockLayers = true ->
    (suffixLayers : List SldLayer) ->
    SldAreConvertibleLayers (topBoundary + bottomBoundary)
      (sldAppendLayers (sldPadLayersBelow bottomBoundary topBlockLayers)
        (sldAppendLayers
          (sldPadLayersAbove (sldLayersTargetArityFrom topBoundary topBlockLayers)
            bottomBlockLayers) suffixLayers))
      (sldAppendLayers (sldPadLayersAbove topBoundary bottomBlockLayers)
        (sldAppendLayers
          (sldPadLayersBelow (sldLayersTargetArityFrom bottomBoundary bottomBlockLayers)
            topBlockLayers) suffixLayers))
  | [], _, _, _, _, _, _ => SldAreConvertibleLayers.fromReflexivity _ _
  | topHead :: topTail, topBoundary, isTopChainComposable, bottomBlockLayers, bottomBoundary,
      isBottomComposable, suffixLayers => by
      have doesHeadMatch : sldLayerSourceArity topHead = topBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isTopChainComposable)
      have doesTailCompose := rightIsTrueOfAndTrue isTopChainComposable
      have slideInstance := sldUpperLayerSlidesDownPastBlock topHead bottomBlockLayers
        bottomBoundary isBottomComposable
        (sldAppendLayers
          (sldPadLayersBelow (sldLayersTargetArityFrom bottomBoundary bottomBlockLayers)
            topTail) suffixLayers)
      rw [doesHeadMatch] at slideInstance
      refine SldAreConvertibleLayers.fromTransitivity
        (SldAreConvertibleLayers.underLayerPrefix (topBoundary + bottomBoundary)
          (sldAppendCells topHead (sldWireLayerOfArity bottomBoundary)) ?_) slideInstance
      rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
      exact sldBlockSlidesDownPastBlock topTail (sldLayerTargetArity topHead)
        doesTailCompose bottomBlockLayers bottomBoundary isBottomComposable suffixLayers

/-- THE ZIP-TO-STACKED CONVERSION: any zip tensor converts to its sequentialized form — top
block first (wires below), then bottom block (wires above).  This is where the exchange
machinery earns its keep: the transported middle-four interchange reduces to block slides on
stacked forms. -/
theorem sldZipConvertsToStackedForm (topFinalArity bottomFinalArity : Nat) :
    (topLayers bottomLayers : List SldLayer) -> (topBoundary bottomBoundary : Nat) ->
    sldLayersAreComposableFrom topBoundary topLayers = true ->
    sldLayersAreComposableFrom bottomBoundary bottomLayers = true ->
    sldLayersTargetArityFrom topBoundary topLayers = topFinalArity ->
    sldLayersTargetArityFrom bottomBoundary bottomLayers = bottomFinalArity ->
    SldAreConvertibleLayers (topBoundary + bottomBoundary)
      (sldZipLayersWithPads topFinalArity bottomFinalArity topLayers bottomLayers)
      (sldAppendLayers (sldPadLayersBelow bottomBoundary topLayers)
        (sldPadLayersAbove topFinalArity bottomLayers))
  | [], bottomLayers, _, _, _, _, _, _ => SldAreConvertibleLayers.fromReflexivity _ _
  | topHead :: topTail, [], topBoundary, bottomBoundary, _, _, _, isBottomReached => by
      have isBottomPinned : bottomBoundary = bottomFinalArity := isBottomReached
      show SldAreConvertibleLayers (topBoundary + bottomBoundary)
        (sldZipLayersWithPads topFinalArity bottomFinalArity (topHead :: topTail) [])
        (sldAppendLayers (sldPadLayersBelow bottomBoundary (topHead :: topTail)) [])
      rw [sldAppendLayersNilRightIsSelf, isBottomPinned]
      exact SldAreConvertibleLayers.fromReflexivity _ _
  | topHead :: topTail, bottomHead :: bottomTail, topBoundary, bottomBoundary,
      isTopComposable, isBottomComposable, willTopReach, willBottomReach => by
      have doesTopHeadMatch : sldLayerSourceArity topHead = topBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isTopComposable)
      have doesBottomHeadMatch : sldLayerSourceArity bottomHead = bottomBoundary :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isBottomComposable)
      have doesTopTailCompose := rightIsTrueOfAndTrue isTopComposable
      have doesBottomTailCompose := rightIsTrueOfAndTrue isBottomComposable
      have willTopTailReach :
          sldLayersTargetArityFrom (sldLayerTargetArity topHead) topTail = topFinalArity :=
        willTopReach
      have willBottomTailReach :
          sldLayersTargetArityFrom (sldLayerTargetArity bottomHead) bottomTail
            = bottomFinalArity :=
        willBottomReach
      have splitStep := SldAreConvertibleLayers.layerSplitTopActsFirst topHead bottomHead
        (sldZipLayersWithPads topFinalArity bottomFinalArity topTail bottomTail)
      rw [sldAppendCellsSourceArity topHead bottomHead, doesTopHeadMatch,
        doesBottomHeadMatch] at splitStep
      have innerStacked := sldZipConvertsToStackedForm topFinalArity bottomFinalArity topTail
        bottomTail (sldLayerTargetArity topHead) (sldLayerTargetArity bottomHead)
        doesTopTailCompose doesBottomTailCompose willTopTailReach willBottomTailReach
      have innerBoundaryEq : sldLayerTargetArity topHead + sldLayerTargetArity bottomHead
          = sldLayerTargetArity
              (sldAppendCells (sldWireLayerOfArity (sldLayerTargetArity topHead))
                bottomHead) := by
        rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
      rw [innerBoundaryEq] at innerStacked
      have midStep := SldAreConvertibleLayers.underLayerPrefix
        (sldLayerTargetArity (sldAppendCells topHead (sldWireLayerOfArity bottomBoundary)))
        (sldAppendCells (sldWireLayerOfArity (sldLayerTargetArity topHead)) bottomHead)
        innerStacked
      have outerMid := SldAreConvertibleLayers.underLayerPrefix
        (topBoundary + bottomBoundary)
        (sldAppendCells topHead (sldWireLayerOfArity bottomBoundary)) midStep
      have lowerSlide := sldLowerLayerSlidesDownPastBlock bottomHead topTail
        (sldLayerTargetArity topHead) doesTopTailCompose
        (sldPadLayersAbove topFinalArity bottomTail)
      rw [doesBottomHeadMatch, willTopTailReach] at lowerSlide
      have headArityEq : sldLayerTargetArity topHead + bottomBoundary
          = sldLayerTargetArity
              (sldAppendCells topHead (sldWireLayerOfArity bottomBoundary)) := by
        rw [sldAppendCellsTargetArity, sldWireLayerTargetArity]
      rw [headArityEq] at lowerSlide
      have slideWrapped := SldAreConvertibleLayers.underLayerPrefix
        (topBoundary + bottomBoundary)
        (sldAppendCells topHead (sldWireLayerOfArity bottomBoundary)) lowerSlide
      exact SldAreConvertibleLayers.fromTransitivity splitStep
        (SldAreConvertibleLayers.fromTransitivity outerMid slideWrapped)

/-! ## THE CONVERTIBILITY TRANSPORT -/

/-- Composability of an embedded diagram's layers at the ORIGINAL source boundary. -/
theorem sldOfWireDiagramLayersComposable {sourceArity targetArity : Nat}
    (diagram : WireDiagram sourceArity targetArity) :
    sldLayersAreComposableFrom sourceArity (sldOfWireDiagram diagram).layers = true := by
  have baseComposable : sldLayersAreComposableFrom (sldOfWireDiagram diagram).sourceArity
      (sldOfWireDiagram diagram).layers = true := sldOfWireDiagramIsComposable diagram
  rw [sldOfWireDiagramSourceArity diagram] at baseComposable
  exact baseComposable

/-- Reach of an embedded diagram's layers from the ORIGINAL source boundary. -/
theorem sldOfWireDiagramLayersReach {sourceArity targetArity : Nat}
    (diagram : WireDiagram sourceArity targetArity) :
    sldLayersTargetArityFrom sourceArity (sldOfWireDiagram diagram).layers = targetArity := by
  have baseReach : sldLayersTargetArityFrom (sldOfWireDiagram diagram).sourceArity
      (sldOfWireDiagram diagram).layers = targetArity := sldOfWireDiagramTargetArity diagram
  rw [sldOfWireDiagramSourceArity diagram] at baseReach
  exact baseReach

/-- CONVERTIBILITY TRANSPORT: every conversion of the binary syntax maps to a conversion of
the strict-layer carrier — induction over the 28 old constructors.  The strict-monoidal glue
constructors land on `rfl`-level structure (identities and reassociations are list
identities), the 18 rows land on the corresponding layer rows at zero pad, the interchange
lands on the block-slide machinery, and the two congruence constructors land on the pad
congruences through the stacked forms. -/
theorem sldOfWireDiagramTransportsConvertibility {sourceArity targetArity : Nat}
    {leftDiagram rightDiagram : WireDiagram sourceArity targetArity}
    (areConvertible : AreConvertibleDiagrams leftDiagram rightDiagram) :
    SldAreConvertibleLayers sourceArity (sldOfWireDiagram leftDiagram).layers
      (sldOfWireDiagram rightDiagram).layers := by
  induction areConvertible with
  | fromReflexivity diagram =>
      exact SldAreConvertibleLayers.fromReflexivity _ _
  | fromSymmetry _ flippedTransported =>
      exact SldAreConvertibleLayers.fromSymmetry flippedTransported
  | fromTransitivity _ _ leftTransported rightTransported =>
      exact SldAreConvertibleLayers.fromTransitivity leftTransported rightTransported
  | @underComposeSequential innerSourceArity middleArity innerTargetArity
      firstLeft firstRight secondLeft secondRight _ _ firstTransported secondTransported =>
      refine SldAreConvertibleLayers.fromTransitivity
        (sldConvAppendsSuffix firstTransported (sldOfWireDiagram secondLeft).layers)
        (sldConvUnderPrefixList (sldOfWireDiagram firstRight).layers innerSourceArity
          (sldOfWireDiagram secondLeft).layers (sldOfWireDiagram secondRight).layers ?_)
      rw [sldOfWireDiagramLayersReach firstRight]
      exact secondTransported
  | @underTensorParallel topSourceArity topTargetArity bottomSourceArity bottomTargetArity
      topLeft topRight bottomLeft bottomRight _ _ topTransported bottomTransported =>
      show SldAreConvertibleLayers (topSourceArity + bottomSourceArity)
        (sldZipLayersWithPads (sldTargetArity (sldOfWireDiagram topLeft))
          (sldTargetArity (sldOfWireDiagram bottomLeft))
          (sldOfWireDiagram topLeft).layers (sldOfWireDiagram bottomLeft).layers)
        (sldZipLayersWithPads (sldTargetArity (sldOfWireDiagram topRight))
          (sldTargetArity (sldOfWireDiagram bottomRight))
          (sldOfWireDiagram topRight).layers (sldOfWireDiagram bottomRight).layers)
      rw [sldOfWireDiagramTargetArity topLeft, sldOfWireDiagramTargetArity bottomLeft,
        sldOfWireDiagramTargetArity topRight, sldOfWireDiagramTargetArity bottomRight]
      have stackedLeft := sldZipConvertsToStackedForm topTargetArity bottomTargetArity
        (sldOfWireDiagram topLeft).layers (sldOfWireDiagram bottomLeft).layers
        topSourceArity bottomSourceArity
        (sldOfWireDiagramLayersComposable topLeft)
        (sldOfWireDiagramLayersComposable bottomLeft)
        (sldOfWireDiagramLayersReach topLeft) (sldOfWireDiagramLayersReach bottomLeft)
      have stackedRight := sldZipConvertsToStackedForm topTargetArity bottomTargetArity
        (sldOfWireDiagram topRight).layers (sldOfWireDiagram bottomRight).layers
        topSourceArity bottomSourceArity
        (sldOfWireDiagramLayersComposable topRight)
        (sldOfWireDiagramLayersComposable bottomRight)
        (sldOfWireDiagramLayersReach topRight) (sldOfWireDiagramLayersReach bottomRight)
      have belowCongruence := sldConvAppendsSuffix
        (sldConvPadsBelow topTransported bottomSourceArity)
        (sldPadLayersAbove topTargetArity (sldOfWireDiagram bottomLeft).layers)
      have aboveCongruence := sldConvPadsAbove bottomTransported topTargetArity
      have prefixReach : sldLayersTargetArityFrom (topSourceArity + bottomSourceArity)
          (sldPadLayersBelow bottomSourceArity (sldOfWireDiagram topRight).layers)
          = topTargetArity + bottomSourceArity := by
        rw [sldPadLayersBelowTargetArityFrom bottomSourceArity
          (sldOfWireDiagram topRight).layers topSourceArity,
          sldOfWireDiagramLayersReach topRight]
      rw [prefixReach.symm] at aboveCongruence
      exact SldAreConvertibleLayers.fromTransitivity stackedLeft
        (SldAreConvertibleLayers.fromTransitivity belowCongruence
          (SldAreConvertibleLayers.fromTransitivity
            (sldConvUnderPrefixList
              (sldPadLayersBelow bottomSourceArity (sldOfWireDiagram topRight).layers)
              (topSourceArity + bottomSourceArity)
              (sldPadLayersAbove topTargetArity (sldOfWireDiagram bottomLeft).layers)
              (sldPadLayersAbove topTargetArity (sldOfWireDiagram bottomRight).layers)
              aboveCongruence)
            (SldAreConvertibleLayers.fromSymmetry stackedRight)))
  | composeIdentitySource diagram =>
      exact SldAreConvertibleLayers.fromReflexivity _ _
  | @composeIdentityTarget caseSourceArity caseTargetArity diagram =>
      show SldAreConvertibleLayers caseSourceArity
        (sldAppendLayers (sldOfWireDiagram diagram).layers []) (sldOfWireDiagram diagram).layers
      rw [sldAppendLayersNilRightIsSelf]
      exact SldAreConvertibleLayers.fromReflexivity caseSourceArity
        (sldOfWireDiagram diagram).layers
  | @composeReassociate caseSourceArity secondArity thirdArity caseTargetArity
      firstStage secondStage thirdStage =>
      show SldAreConvertibleLayers caseSourceArity
        (sldAppendLayers
          (sldAppendLayers (sldOfWireDiagram firstStage).layers
            (sldOfWireDiagram secondStage).layers)
          (sldOfWireDiagram thirdStage).layers)
        (sldAppendLayers (sldOfWireDiagram firstStage).layers
          (sldAppendLayers (sldOfWireDiagram secondStage).layers
            (sldOfWireDiagram thirdStage).layers))
      rw [sldAppendLayersAssoc]
      exact SldAreConvertibleLayers.fromReflexivity caseSourceArity _
  | tensorIdentityFusion topStrandCount bottomStrandCount =>
      exact SldAreConvertibleLayers.fromReflexivity (topStrandCount + bottomStrandCount) []
  | @middleFourInterchange topSourceArity topMiddleArity topTargetArity
      bottomSourceArity bottomMiddleArity bottomTargetArity
      topFirst topSecond bottomFirst bottomSecond =>
      show SldAreConvertibleLayers (topSourceArity + bottomSourceArity)
        (sldZipLayersWithPads
          (sldTargetArity
            (sldOfWireDiagram (WireDiagram.composeSequential topFirst topSecond)))
          (sldTargetArity
            (sldOfWireDiagram (WireDiagram.composeSequential bottomFirst bottomSecond)))
          (sldAppendLayers (sldOfWireDiagram topFirst).layers
            (sldOfWireDiagram topSecond).layers)
          (sldAppendLayers (sldOfWireDiagram bottomFirst).layers
            (sldOfWireDiagram bottomSecond).layers))
        (sldAppendLayers
          (sldZipLayersWithPads (sldTargetArity (sldOfWireDiagram topFirst))
            (sldTargetArity (sldOfWireDiagram bottomFirst))
            (sldOfWireDiagram topFirst).layers (sldOfWireDiagram bottomFirst).layers)
          (sldZipLayersWithPads (sldTargetArity (sldOfWireDiagram topSecond))
            (sldTargetArity (sldOfWireDiagram bottomSecond))
            (sldOfWireDiagram topSecond).layers (sldOfWireDiagram bottomSecond).layers))
      rw [sldOfWireDiagramTargetArity (WireDiagram.composeSequential topFirst topSecond),
        sldOfWireDiagramTargetArity (WireDiagram.composeSequential bottomFirst bottomSecond),
        sldOfWireDiagramTargetArity topFirst, sldOfWireDiagramTargetArity bottomFirst,
        sldOfWireDiagramTargetArity topSecond, sldOfWireDiagramTargetArity bottomSecond]
      have compTopWhole : sldLayersAreComposableFrom topSourceArity
          (sldAppendLayers (sldOfWireDiagram topFirst).layers
            (sldOfWireDiagram topSecond).layers) = true :=
        sldOfWireDiagramLayersComposable (WireDiagram.composeSequential topFirst topSecond)
      have reachTopWhole : sldLayersTargetArityFrom topSourceArity
          (sldAppendLayers (sldOfWireDiagram topFirst).layers
            (sldOfWireDiagram topSecond).layers) = topTargetArity :=
        sldOfWireDiagramLayersReach (WireDiagram.composeSequential topFirst topSecond)
      have compBottomWhole : sldLayersAreComposableFrom bottomSourceArity
          (sldAppendLayers (sldOfWireDiagram bottomFirst).layers
            (sldOfWireDiagram bottomSecond).layers) = true :=
        sldOfWireDiagramLayersComposable
          (WireDiagram.composeSequential bottomFirst bottomSecond)
      have reachBottomWhole : sldLayersTargetArityFrom bottomSourceArity
          (sldAppendLayers (sldOfWireDiagram bottomFirst).layers
            (sldOfWireDiagram bottomSecond).layers) = bottomTargetArity :=
        sldOfWireDiagramLayersReach (WireDiagram.composeSequential bottomFirst bottomSecond)
      have stackedWhole := sldZipConvertsToStackedForm topTargetArity bottomTargetArity
        (sldAppendLayers (sldOfWireDiagram topFirst).layers
          (sldOfWireDiagram topSecond).layers)
        (sldAppendLayers (sldOfWireDiagram bottomFirst).layers
          (sldOfWireDiagram bottomSecond).layers)
        topSourceArity bottomSourceArity compTopWhole compBottomWhole
        reachTopWhole reachBottomWhole
      rw [sldPadLayersBelowOfAppend bottomSourceArity (sldOfWireDiagram topFirst).layers
          (sldOfWireDiagram topSecond).layers,
        sldPadLayersAboveOfAppend topTargetArity (sldOfWireDiagram bottomFirst).layers
          (sldOfWireDiagram bottomSecond).layers,
        sldAppendLayersAssoc
          (sldPadLayersBelow bottomSourceArity (sldOfWireDiagram topFirst).layers)
          (sldPadLayersBelow bottomSourceArity (sldOfWireDiagram topSecond).layers)
          (sldAppendLayers
            (sldPadLayersAbove topTargetArity (sldOfWireDiagram bottomFirst).layers)
            (sldPadLayersAbove topTargetArity (sldOfWireDiagram bottomSecond).layers))]
        at stackedWhole
      have middleSlide := sldBlockSlidesDownPastBlock (sldOfWireDiagram topSecond).layers
        topMiddleArity (sldOfWireDiagramLayersComposable topSecond)
        (sldOfWireDiagram bottomFirst).layers bottomSourceArity
        (sldOfWireDiagramLayersComposable bottomFirst)
        (sldPadLayersAbove topTargetArity (sldOfWireDiagram bottomSecond).layers)
      rw [sldOfWireDiagramLayersReach topSecond, sldOfWireDiagramLayersReach bottomFirst]
        at middleSlide
      have slidPrefixReach : sldLayersTargetArityFrom (topSourceArity + bottomSourceArity)
          (sldPadLayersBelow bottomSourceArity (sldOfWireDiagram topFirst).layers)
          = topMiddleArity + bottomSourceArity := by
        rw [sldPadLayersBelowTargetArityFrom bottomSourceArity
          (sldOfWireDiagram topFirst).layers topSourceArity,
          sldOfWireDiagramLayersReach topFirst]
      rw [slidPrefixReach.symm] at middleSlide
      have middleUnderPrefix := sldConvUnderPrefixList
        (sldPadLayersBelow bottomSourceArity (sldOfWireDiagram topFirst).layers)
        (topSourceArity + bottomSourceArity) _ _ middleSlide
      rw [(sldAppendLayersAssoc
        (sldPadLayersBelow bottomSourceArity (sldOfWireDiagram topFirst).layers)
        (sldPadLayersAbove topMiddleArity (sldOfWireDiagram bottomFirst).layers)
        (sldAppendLayers
          (sldPadLayersBelow bottomMiddleArity (sldOfWireDiagram topSecond).layers)
          (sldPadLayersAbove topTargetArity (sldOfWireDiagram bottomSecond).layers))).symm]
        at middleUnderPrefix
      have stackedFirst := sldZipConvertsToStackedForm topMiddleArity bottomMiddleArity
        (sldOfWireDiagram topFirst).layers (sldOfWireDiagram bottomFirst).layers
        topSourceArity bottomSourceArity
        (sldOfWireDiagramLayersComposable topFirst)
        (sldOfWireDiagramLayersComposable bottomFirst)
        (sldOfWireDiagramLayersReach topFirst) (sldOfWireDiagramLayersReach bottomFirst)
      have stackedSecond := sldZipConvertsToStackedForm topTargetArity bottomTargetArity
        (sldOfWireDiagram topSecond).layers (sldOfWireDiagram bottomSecond).layers
        topMiddleArity bottomMiddleArity
        (sldOfWireDiagramLayersComposable topSecond)
        (sldOfWireDiagramLayersComposable bottomSecond)
        (sldOfWireDiagramLayersReach topSecond) (sldOfWireDiagramLayersReach bottomSecond)
      have firstBack := sldConvAppendsSuffix
        (SldAreConvertibleLayers.fromSymmetry stackedFirst)
        (sldAppendLayers
          (sldPadLayersBelow bottomMiddleArity (sldOfWireDiagram topSecond).layers)
          (sldPadLayersAbove topTargetArity (sldOfWireDiagram bottomSecond).layers))
      have zipFirstReach : sldLayersTargetArityFrom (topSourceArity + bottomSourceArity)
          (sldZipLayersWithPads topMiddleArity bottomMiddleArity
            (sldOfWireDiagram topFirst).layers (sldOfWireDiagram bottomFirst).layers)
          = topMiddleArity + bottomMiddleArity :=
        sldZipLayersTargetArityFrom topMiddleArity bottomMiddleArity
          (sldOfWireDiagram topFirst).layers (sldOfWireDiagram bottomFirst).layers
          topSourceArity bottomSourceArity
          (sldOfWireDiagramLayersReach topFirst) (sldOfWireDiagramLayersReach bottomFirst)
      have secondBack := SldAreConvertibleLayers.fromSymmetry stackedSecond
      rw [zipFirstReach.symm] at secondBack
      exact SldAreConvertibleLayers.fromTransitivity stackedWhole
        (SldAreConvertibleLayers.fromTransitivity middleUnderPrefix
          (SldAreConvertibleLayers.fromTransitivity firstBack
            (sldConvUnderPrefixList
              (sldZipLayersWithPads topMiddleArity bottomMiddleArity
                (sldOfWireDiagram topFirst).layers (sldOfWireDiagram bottomFirst).layers)
              (topSourceArity + bottomSourceArity) _ _ secondBack)))
  | fromAddAssociativityRow => exact SldAreConvertibleLayers.fromAddAssociativityRow 0 0 []
  | fromAddLeftUnitRow => exact SldAreConvertibleLayers.fromAddLeftUnitRow 0 0 []
  | fromAddRightUnitRow => exact SldAreConvertibleLayers.fromAddRightUnitRow 0 0 []
  | fromAddCommutativityRow => exact SldAreConvertibleLayers.fromAddCommutativityRow 0 0 []
  | fromCopyCoassociativityRow =>
      exact SldAreConvertibleLayers.fromCopyCoassociativityRow 0 0 []
  | fromCopyLeftCounitRow => exact SldAreConvertibleLayers.fromCopyLeftCounitRow 0 0 []
  | fromCopyRightCounitRow => exact SldAreConvertibleLayers.fromCopyRightCounitRow 0 0 []
  | fromCopyCocommutativityRow =>
      exact SldAreConvertibleLayers.fromCopyCocommutativityRow 0 0 []
  | fromCopyAfterAddBimonoidRow => exact SldAreConvertibleLayers.fromBimonoidSquareRow 0 0 []
  | fromCopyAfterZeroBimonoidRow => exact SldAreConvertibleLayers.fromCopyAfterZeroRow 0 0 []
  | fromDiscardAfterAddBimonoidRow =>
      exact SldAreConvertibleLayers.fromDiscardAfterAddRow 0 0 []
  | fromDiscardAfterZeroBimonoidRow =>
      exact SldAreConvertibleLayers.fromDiscardAfterZeroRow 0 0 []
  | fromSwapInvolutionRow => exact SldAreConvertibleLayers.fromSwapInvolutionRow 0 0 []
  | fromSwapYangBaxterRow => exact SldAreConvertibleLayers.fromSwapYangBaxterRow 0 0 []
  | fromSwapPastAddNaturalityRow => exact SldAreConvertibleLayers.fromSwapPastAddRow 0 0 []
  | fromSwapPastZeroNaturalityRow => exact SldAreConvertibleLayers.fromSwapPastZeroRow 0 0 []
  | fromCopyPastSwapNaturalityRow => exact SldAreConvertibleLayers.fromCopyPastSwapRow 0 0 []
  | fromDiscardPastSwapNaturalityRow =>
      exact SldAreConvertibleLayers.fromDiscardPastSwapRow 0 0 []

/-- Diagram-level transport corollary. -/
theorem sldOfWireDiagramTransportsToDiagrams {sourceArity targetArity : Nat}
    {leftDiagram rightDiagram : WireDiagram sourceArity targetArity}
    (areConvertible : AreConvertibleDiagrams leftDiagram rightDiagram) :
    sldAreConvertibleDiagrams (sldOfWireDiagram leftDiagram) (sldOfWireDiagram rightDiagram) := by
  refine ⟨?_, ?_⟩
  · rw [sldOfWireDiagramSourceArity leftDiagram, sldOfWireDiagramSourceArity rightDiagram]
  · rw [sldOfWireDiagramSourceArity leftDiagram]
    exact sldOfWireDiagramTransportsConvertibility areConvertible

/-- TRANSPORT FIRE: the r30 refuted unit pair, transported from the OLD congruence's one-row
derivation into the layer congruence. -/
theorem sldTransportedUnitPairFires :
    SldAreConvertibleLayers 1 (sldOfWireDiagram refutedUnitPairLeftSide).layers
      (sldOfWireDiagram (WireDiagram.identityWires 1)).layers :=
  sldOfWireDiagramTransportsConvertibility refutedUnitPairIsNowConvertible

/-- TRANSPORT FIRE: the r1 derived three-step chain (congruence + row + identity law). -/
theorem sldTransportedDerivedChainFires :
    SldAreConvertibleLayers 0 (sldOfWireDiagram derivedZeroThenLeftUnitChain).layers
      (sldOfWireDiagram WireDiagram.zeroGen).layers :=
  sldOfWireDiagramTransportsConvertibility derivedZeroThenLeftUnitChainConverts

/-! ## Markers -/

/-- Stage-E marker: the embedding transport LANDED — `AreConvertibleDiagrams d e` maps to
`SldAreConvertibleLayers` on the embedded layers, all 28 constructors, zero-axiom. -/
def fxLafontStrictLayer_hasEmbeddingTransport : Bool := true

/-- Stage-F marker (honest false): the canonical-reduction / completeness attack over the NEW
carrier (every well-formed `SldDiagram` converts to a canonical form determined by its
matrix, [Lafont2003] staircase route) is NOT attempted in this round.  The padding
obstruction that REFUTED the old statement is gone (`sldEmbeddingDissolvesTheSeparator`);
what remains is the genuine Lafont normal-form grind, stated as the next commission's
target, not walled — no impossibility is claimed. -/
def fxLafontStrictLayer_hasCanonicalCompleteness : Bool := false

#eval decide (sldIsComposable (sldOfWireDiagram copyAfterAddRightSide) = true)
#eval decide (sldTargetArity (sldOfWireDiagram copyAfterAddRightSide) = 2)
#eval decide (doEntriesAgreeUpTo 2 2 (sldDenote (sldOfWireDiagram copyAfterAddRightSide))
  (denoteEntries copyAfterAddRightSide) = true)
#eval decide (doEntriesAgreeUpTo 2 1
  (sldDenote (sldOfWireDiagram leftPaddedCopyDiagram))
  (sldDenote (sldOfWireDiagram WireDiagram.copyGen)) = true)

end FX1Poly.Polygraph.Omega.LafontProp
