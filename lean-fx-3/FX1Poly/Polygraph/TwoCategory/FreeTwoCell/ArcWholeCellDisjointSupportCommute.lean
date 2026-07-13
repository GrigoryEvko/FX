import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCellPastCellSwapSimCount

/-! # MODE-COMMUTE r28 — the whole-cell commutation at the GODEMENT INNER SHAPE + the four-pin adjudication

## What this ships (Brick 4)

  * **`arcGodementInnerSwapSimCount`** — `cellPastCell` packaged at the literal Godement inner
    shape (`ArcGodementCoreSwapSimCount`'s two run orders: `cellAlphaUpper` whiskered
    `(leftAcc, gX . rightAcc)`, `cellBeta` whiskered `(leftAcc . fX, rightAcc)`), obtained at
    `gapPath := identityPath` with the whisker composites collapsed by
    `composePath_identityPath_right`.  This is the whole-cell disjoint-support commutation in the
    exact orientation every parent consumer names — fired on a cap-bearing instance.
  * **`arcWhiskerSupportListEquality_refutedOnGenCells`** — ★ the `:234` VERBATIM-shape
    adjudication: the pin's literal demand `reduct.links = renameLinks sigma redex.links` (with
    `sigma` the r22 `compoundFreshBlockTransposition`) is FALSE already for two SINGLE-CUP cells:
    fresh allocation is position-independent, so the two orders produce BYTE-IDENTICAL link lists,
    while the compound sigma permutes the two blocks — the renamed list has its entries in swapped
    order.  Machine-refuted (`decide`).  The pin can therefore NEVER flip on its verbatim demand;
    the order-insensitive `ArcStepSimCount` form (Brick 3 + this packaging) is the honest
    whole-cell content — exactly the r24 WRONG-TARGET flag, now with a kernel-checked witness at
    the pin's own term shape.

## The four-pin adjudication (each pin read verbatim, none flipped)

  * `fxMode_hasDisjointWhiskerSupport` (`ArcDisjointWhiskerSupport.lean:234`) — demands the
    links-LIST equality over unbounded `runArcCell` cells.  REFUTED-as-shaped here on gen cells;
    stays `false` permanently; successor content = `arcGodementInnerSwapSimCount`.
  * `fxMode_hasArcGodementSwapRenameableProof2` (`WalkingAdjunction/ArcSwapRenameable.lean:3046`)
    — residual (2) demands `ArcGodementCoreSwapSimCount`: the existential over ARBITRARY
    fresh/forest/non-degenerate states (no window decomposition, no component-disjointness) and
    arbitrary cells INCLUDING box atoms.  NOT delivered: this run's content is the guarded
    turnback-only core.  Precise deltas: (a) box-atom arms (the box step's `2 * numConsumed`
    removal sits outside the segment discipline); (b) the unguarded seed — the r26 pre-bridged
    counterexamples show the guard is load-bearing for the CONCRETE carriers, and whether the bare
    existential survives arbitrary pre-bridged seeds is undecided here.  Stays `false`.
  * `fxMode_hasArcPartitionCommuteProof` (`GodementIndependence.lean:525`) — REFUTED as stated
    (over every state) by `not_arcGodementPartitionCommute`; the owner records it can never flip.
  * `fxMode_hasArcGodementSamePartitionFreshProof` (`ArcPartitionCommute.lean:545`) — the owner's
    statement is machine-refuted (r24 note); never flipped.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` + independent `#print axioms` twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The Godement inner-shape packaging -/

/-- ★★★ **The whole-cell disjoint-support commutation at the Godement inner shape.**  The two run
orders of `ArcGodementCoreSwapSimCount` — `cellAlphaUpper` at `(leftAcc, gLow . rightAcc)` then
`cellBeta` at `(leftAcc . fHigh, rightAcc)`, versus `cellBeta` at `(leftAcc . fMid, rightAcc)`
then `cellAlphaUpper` at `(leftAcc, gMid . rightAcc)` — are `ArcStepSimCount`-related with a
bounded composite carrier, for turnback-only cells over a decomposed well-formed state with
component-disjoint windows.  `cellPastCell` at `gapPath := identityPath`, whisker composites
collapsed by the path right-identity law. -/
theorem arcGodementInnerSwapSimCount {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid : ModalityPath signature.graph middleMode targetMode}
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (state : ArcWireState) (leftPad fSegment gSegment suffixWires : List Nat)
    (wellFormed : WellFormedArcState state)
    (alphaTurnback : cellAlphaUpper.isTurnbackOnly = true)
    (betaTurnback : cellBeta.isTurnbackOnly = true)
    (decomp : state.openWires = leftPad ++ (fSegment ++ ([] ++ (gSegment ++ suffixWires))))
    (padLen : leftPad.length = leftAcc.length)
    (fSegLen : fSegment.length = fMid.length)
    (gSegLen : gSegment.length = gLow.length)
    (windowsDisjoint : arcWindowsComponentDisjoint state.links fSegment gSegment) :
    ∃ sigma,
      ArcBoundedSwapCarrier state.nextFresh
          (runArcCell (runArcCell state leftAcc (composePath gLow rightAcc) cellAlphaUpper)
            (composePath leftAcc fHigh) rightAcc cellBeta).nextFresh sigma
        ∧ ArcStepSimCount sigma
            (runArcCell (runArcCell state leftAcc (composePath gLow rightAcc) cellAlphaUpper)
              (composePath leftAcc fHigh) rightAcc cellBeta)
            (runArcCell (runArcCell state (composePath leftAcc fMid) rightAcc cellBeta)
              leftAcc (composePath gMid rightAcc) cellAlphaUpper) := by
  obtain ⟨sigma, carrier, simulation⟩ :=
    arcCellPastCellSwapSimCount cellAlphaUpper cellBeta leftAcc (identityPath middleMode)
      (composePath gLow rightAcc) (composePath gMid rightAcc) rightAcc state leftPad fSegment
      [] gSegment suffixWires wellFormed alphaTurnback betaTurnback decomp padLen fSegLen rfl
      gSegLen windowsDisjoint
  rw [composePath_identityPath_right fHigh] at simulation carrier
  rw [composePath_identityPath_right fMid] at simulation
  exact ⟨sigma, carrier, simulation⟩

/-- ★ **The packaging FIRED on a cap-bearing Godement instance**: the whisker-sandwiched counit
cell (f-window `[2,3,4,5]`) against the three-atom cup/cup/cap cell (g-window empty, `gLow` the
identity path), from the six-wire seed — the literal inner-shape orientation. -/
theorem arcGodementInnerSwap_firedOnCounitInstance :
    ∃ sigma,
      ArcBoundedSwapCarrier arcCellPastCellCapFireSeed.nextFresh
          (runArcCell (runArcCell arcCellPastCellCapFireSeed adjunctionLeftThenRight
              (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
                (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
              whiskerSandwichedCounitCell)
            (composePath adjunctionLeftThenRight adjunctionLeftThenRight)
            (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
            threeAtomTurnbackCell).nextFresh sigma
        ∧ ArcStepSimCount sigma
            (runArcCell (runArcCell arcCellPastCellCapFireSeed adjunctionLeftThenRight
                (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
                  (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
                whiskerSandwichedCounitCell)
              (composePath adjunctionLeftThenRight adjunctionLeftThenRight)
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
              threeAtomTurnbackCell)
            (runArcCell (runArcCell arcCellPastCellCapFireSeed
                (composePath adjunctionLeftThenRight
                  (composePath adjunctionLeftThenRight adjunctionLeftThenRight))
                (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
                threeAtomTurnbackCell)
              adjunctionLeftThenRight
              (composePath adjunctionLeftThenRight
                (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
              whiskerSandwichedCounitCell) :=
  arcGodementInnerSwapSimCount whiskerSandwichedCounitCell threeAtomTurnbackCell
    adjunctionLeftThenRight (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    arcCellPastCellCapFireSeed [0, 1] [2, 3, 4, 5] [] []
    arcCellPastCellCapFireSeed_isWellFormed rfl threeAtomTurnbackCell_isTurnbackOnly rfl rfl
    rfl rfl (fun _ _ _ gWireMem => nomatch gWireMem)

/-! ## The `:234` verbatim-shape refutation on gen cells -/

/-- The bare unit cup as a typed cell fixture (`nil => [left,right]`). -/
def unitCupCell : RawTwoCellExpr adjunctionModeSignature
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) adjunctionLeftThenRight :=
  RawTwoCellExpr.gen AdjunctionTwoCell.unit

/-- ★★ **The `:234` links-LIST equality is FALSE for genuine cells** — the pin's verbatim target
`reduct.links = renameLinks (compoundFreshBlockTransposition base wA wB) redex.links`, at two
single-cup cells (`.gen unit` twice, widths `3, 3`, base `2`) over the two-wire seed: BOTH run
orders produce the byte-identical link list `[(7,6),(5,6),(4,3),(2,3)]` (fresh allocation is
position-independent), while the compound sigma swaps the two three-blocks, permuting the list to
`[(4,3),(2,3),(7,6),(5,6)]`.  Kernel-decided.  The order-SENSITIVE list shape can never flip;
the order-INSENSITIVE `ArcStepSimCount` (Brick 3) is the honest whole-cell content. -/
theorem arcWhiskerSupportListEquality_refutedOnGenCells :
    ¬ ((runArcCell (runArcCell arcCupPastCellFireSeed adjunctionLeftThenRight
          (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
          unitCupCell)
        (identityPath (graph := adjunctionGraph) AdjunctionMode.base) adjunctionLeftThenRight
        unitCupCell).links
      = renameLinks (compoundFreshBlockTransposition 2 3 3)
          (runArcCell (runArcCell arcCupPastCellFireSeed (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
              adjunctionLeftThenRight unitCupCell)
            adjunctionLeftThenRight (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
            unitCupCell).links) := by
  decide

/-- The positive counterpart pin: the two orders' link lists are BYTE-IDENTICAL on the same
instance (the reason the renaming shape fails: there is nothing to rename).  `rfl`. -/
theorem arcWhiskerSupportGenCells_linksLiterallyEqual :
    (runArcCell (runArcCell arcCupPastCellFireSeed adjunctionLeftThenRight
          (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
          unitCupCell)
        (identityPath (graph := adjunctionGraph) AdjunctionMode.base) adjunctionLeftThenRight
        unitCupCell).links
      = (runArcCell (runArcCell arcCupPastCellFireSeed (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
            adjunctionLeftThenRight unitCupCell)
          adjunctionLeftThenRight (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
          unitCupCell).links := rfl

/-! ## Honesty markers + the adjudicated pins -/

/-- **Honesty marker — the whole-cell disjoint-support commutation is DELIVERED at the Godement
inner shape** (sim form, bounded carrier, turnback-only cells, decomposed guarded state), and the
`:234` verbatim list shape is machine-refuted on gen cells.  `= true`. -/
def fxMode_hasWholeCellDisjointSupportCommute : Bool := true

/-- **Adjudication pin — `:234` stays `false` PERMANENTLY on its verbatim demand.**  The demanded
links-list equality is refuted here on gen cells (`arcWhiskerSupportListEquality_refutedOnGenCells`);
the successor content is `arcGodementInnerSwapSimCount`.  `rfl`. -/
theorem arcWholeCellCommute_disjointWhiskerSupport_stays_false :
    fxMode_hasDisjointWhiskerSupport = false := rfl

/-- **Adjudication pin — `:3046` residual (2) stays OPEN**: `ArcGodementCoreSwapSimCount` as
stated (arbitrary seeds, box atoms, no guard) is NOT what this run delivers; deltas recorded in
the file header.  `rfl`. -/
theorem arcWholeCellCommute_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

/-- **Adjudication pin — `:525` stays `false`** (refuted-as-stated at the owner; never
flippable).  `rfl`. -/
theorem arcWholeCellCommute_partitionCommute_stays_false :
    fxMode_hasArcPartitionCommuteProof = false := rfl

/-- **Adjudication pin — `:545` stays `false`** (machine-refuted-as-stated at the owner; the
bundle EXCLUDES its counterexample rather than re-proving it).  `rfl`. -/
theorem arcWholeCellCommute_samePartitionFresh_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

/-- **Adjudication pin — the block-commute keystone (`GodementIndependence`) stays `false`**: it
names the ∀-state extract commutation whose partition core is refuted; the guarded sim-form
delivered here is the live successor content the dispatch lane can consume.  `rfl`. -/
theorem arcWholeCellCommute_blockCommute_stays_false :
    fxMode_hasArcBlockCommuteProof = false := rfl

end FX1Poly.Polygraph
