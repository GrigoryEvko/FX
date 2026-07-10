import FX1Poly.Polygraph.Omega.Steiner.WallHarvestWithId

/-! # Polygraph/Omega/Steiner/VaryingWhiskerReconstruct — the VARYING-whisker map-IN reconstruct (OMEGA-3 r3, B1)

★ **The general varying-whisker reconstruct.**  `WallHarvestWithId` shipped the FIXED-whisker completeness
`whiskeredAtomWord_conv_iff_linearizeFull_eq` (`w` held constant, only the whiskered interior varies).  This
file lands the honest open work the r2 ledger named (`fxOmega3_generalWhiskeredMapInOpenR2`): the fragment
where the WHISKERING 1-cell itself varies — `whiskerLeft whiskerA cellA` vs `whiskerLeft whiskerB cellB` with
`whiskerA ≠ whiskerB`.  The `→` (chain soundness `linearizeFull_eq_of_saturatedConvWithId`) was already
shipped; the `←` reconstruct is the deliverable.

## The readback (the staircase-reify shape, both axes read off the chain table)

Two orthogonal reconstructions, composed by `trans` through the two whiskering-1-cell congruences the r2
sibling added:

  * **Whisker axis (read the whisker off the SOURCE pole).**  `linearizeFull_bsCoord_eq` gives the
    top-adjacent source-pole equality.  For an atom-word interior, `boundarySource cellA = crownBaseCell`
    (`boundarySource_atomWord`) linearizes to the degenerate zero table, so the pole
    `addCoordinates (linearize whiskerA) 0` cancels (`addCoordinates_zeroVector_right`) to `linearize whiskerA`
    — the whisker atom count is faithfully recorded there.  Equal poles give `linearize whiskerA =
    linearize whiskerB`; `atomWord_conv_of_linearize_eq` reconstructs the whisker convertibility and
    `SaturatedConvOverWithId.whiskerLeftWhiskerCongr` re-whiskers with it (whisker varies, interior fixed).

  * **Interior axis (read the interior off the TOP row).**  `linearizeFull_topCoord_eq` gives the top-row
    equality, which forgets the whisker (`linearize_whiskerLeft`), so it IS `linearize cellA = linearize cellB`;
    `atomWord_conv_of_linearize_eq` reconstructs the interior convertibility and
    `SaturatedConvOverWithId.whiskerLeftCongr` re-whiskers it (interior varies, whisker fixed).

The right-whisker dual is symmetric (the whisker sits on the RIGHT of the boundary vcomp, so the pole cancels
by `addCoordinates_zeroVector_left`, and the two duals `whiskerRightWhiskerCongr` / `whiskerRightCongr` glue).

## Honest scope (recon JOB 2/4, executed)

This is scoped to the CROWN single-generator atom-word fragment, where the abelian `linearize` is a complete
invariant (the free monoid on ONE generator is abelian).  The multi-generator (ambient width ≥ 2) case is NOT
this lemma: at cell-dimension 1 the abelian table conflates `g1 . g2` with `g2 . g1` on a NON-abelian free
monoid — a genuine invariant-side wall named in `SuspensionWithIdLedger`
(`fxOmega3_multiGeneratorDimOneNonAbelianWallR3`).  The FORM-A undecidability ceiling (`CeilingLift.lean`)
does not bleed in: on the crown atom-word fragment the word problem is free.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! ## B1 truth-probe — the reify on concrete table-equal varying-whisker pairs -/

/-- Probe: differently-associated 3-atom whiskers over differently-associated 3-atom interiors have
EQUAL whiskered chain tables (varying whisker + varying interior, both table-matched). -/
example : linearizeFull crownValuation (CellExpr.whiskerLeft dimTwoWordRight word3Right)
    = linearizeFull crownValuation (CellExpr.whiskerLeft dimTwoWordLeft word3Left) := by decide

/-- Probe: whiskers of unequal atom count (3 vs 2) give DISTINCT whiskered chain tables. -/
example : linearizeFull crownValuation (CellExpr.whiskerLeft dimTwoWordRight word3Right)
    ≠ linearizeFull crownValuation (CellExpr.whiskerLeft dimTwoWordTwo word3Right) := by decide

/-! ## The left varying-whisker reconstruct -/

/-- ★★ **THE VARYING-WHISKER RECONSTRUCT (`←`, left whisker).**  For atom-word whiskers AND atom-word
interiors, equal whiskered chain tables reconstruct sibling convertibility even when the WHISKERING cell
varies: the source pole gives the whisker convertibility, the top row gives the interior convertibility, and
the two whiskering-1-cell congruences compose them. -/
theorem whiskeredVaryingWhisker_conv_of_linearizeFull_eq {dim : Nat}
    {whiskerA whiskerB : CellExpr crownComputad (dim + 1)}
    {cellA cellB : CellExpr crownComputad (dim + 2)}
    (hWhiskerA : IsAtomWord whiskerA) (hWhiskerB : IsAtomWord whiskerB)
    (hCellA : IsAtomWord cellA) (hCellB : IsAtomWord cellB)
    (chainEqual : linearizeFull crownValuation (CellExpr.whiskerLeft whiskerA cellA)
      = linearizeFull crownValuation (CellExpr.whiskerLeft whiskerB cellB)) :
    SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad)
      (CellExpr.whiskerLeft whiskerA cellA) (CellExpr.whiskerLeft whiskerB cellB) := by
  -- Whisker axis: read the whisker off the source pole (the interior boundary is degenerate).
  have poleReduceA :
      (linearize crownValuation (boundarySource (CellExpr.whiskerLeft whiskerA cellA))).coordinates
        = (linearize crownValuation whiskerA).coordinates := by
    have hzero : (linearize crownValuation (crownBaseCell (dim + 1))).coordinates
        = zeroVector (linearize crownValuation whiskerA).coordinates.length := by
      rw [linearize_length crownValuation whiskerA]
      rfl
    calc (linearize crownValuation (boundarySource (CellExpr.whiskerLeft whiskerA cellA))).coordinates
        = addCoordinates (linearize crownValuation whiskerA).coordinates
            (linearize crownValuation (boundarySource cellA)).coordinates := rfl
      _ = addCoordinates (linearize crownValuation whiskerA).coordinates
            (linearize crownValuation (crownBaseCell (dim + 1))).coordinates := by
              rw [boundarySource_atomWord hCellA]
      _ = addCoordinates (linearize crownValuation whiskerA).coordinates
            (zeroVector (linearize crownValuation whiskerA).coordinates.length) := by rw [hzero]
      _ = (linearize crownValuation whiskerA).coordinates := addCoordinates_zeroVector_right _
  have poleReduceB :
      (linearize crownValuation (boundarySource (CellExpr.whiskerLeft whiskerB cellB))).coordinates
        = (linearize crownValuation whiskerB).coordinates := by
    have hzero : (linearize crownValuation (crownBaseCell (dim + 1))).coordinates
        = zeroVector (linearize crownValuation whiskerB).coordinates.length := by
      rw [linearize_length crownValuation whiskerB]
      rfl
    calc (linearize crownValuation (boundarySource (CellExpr.whiskerLeft whiskerB cellB))).coordinates
        = addCoordinates (linearize crownValuation whiskerB).coordinates
            (linearize crownValuation (boundarySource cellB)).coordinates := rfl
      _ = addCoordinates (linearize crownValuation whiskerB).coordinates
            (linearize crownValuation (crownBaseCell (dim + 1))).coordinates := by
              rw [boundarySource_atomWord hCellB]
      _ = addCoordinates (linearize crownValuation whiskerB).coordinates
            (zeroVector (linearize crownValuation whiskerB).coordinates.length) := by rw [hzero]
      _ = (linearize crownValuation whiskerB).coordinates := addCoordinates_zeroVector_right _
  have whiskerCoordEq : (linearize crownValuation whiskerA).coordinates
      = (linearize crownValuation whiskerB).coordinates :=
    poleReduceA.symm.trans ((linearizeFull_bsCoord_eq crownValuation chainEqual).trans poleReduceB)
  have whiskerConv : SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad) whiskerA whiskerB :=
    embedSaturatedConvOver
      (atomWord_conv_of_linearize_eq hWhiskerA hWhiskerB (congrArg SteinerCell.mk whiskerCoordEq))
  -- Interior axis: read the interior off the top row (the whisker is forgotten there).
  have interiorTableEq : linearize crownValuation cellA = linearize crownValuation cellB := by
    have topRow := linearizeFull_topCoord_eq crownValuation chainEqual
    exact congrArg SteinerCell.mk topRow
  have interiorConv : SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad) cellA cellB :=
    embedSaturatedConvOver (atomWord_conv_of_linearize_eq hCellA hCellB interiorTableEq)
  exact SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.whiskerLeftWhiskerCongr cellA whiskerConv)
    (SaturatedConvOverWithId.whiskerLeftCongr whiskerB interiorConv)

/-- ★★ **THE VARYING-WHISKER CROWN (left).**  On the whiskered atom-word fragment with the WHISKERING cell
free to vary, sibling convertibility IS whiskered chain-table equality both ways. -/
theorem whiskeredVaryingWhisker_conv_iff_linearizeFull_eq {dim : Nat}
    {whiskerA whiskerB : CellExpr crownComputad (dim + 1)}
    {cellA cellB : CellExpr crownComputad (dim + 2)}
    (hWhiskerA : IsAtomWord whiskerA) (hWhiskerB : IsAtomWord whiskerB)
    (hCellA : IsAtomWord cellA) (hCellB : IsAtomWord cellB) :
    SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad)
        (CellExpr.whiskerLeft whiskerA cellA) (CellExpr.whiskerLeft whiskerB cellB)
      ↔ linearizeFull crownValuation (CellExpr.whiskerLeft whiskerA cellA)
          = linearizeFull crownValuation (CellExpr.whiskerLeft whiskerB cellB) :=
  ⟨fun conv => linearizeFull_eq_of_saturatedConvWithId crownValuation conv,
   whiskeredVaryingWhisker_conv_of_linearizeFull_eq hWhiskerA hWhiskerB hCellA hCellB⟩

/-! ## The right varying-whisker reconstruct (the dual) -/

/-- ★★ **THE VARYING-WHISKER RECONSTRUCT (`←`, right whisker).**  The dual of the left reconstruct: the
whisker sits on the RIGHT of the boundary vcomp, so the source pole cancels by `addCoordinates_zeroVector_left`
and the two RIGHT whiskering congruences (`whiskerRightWhiskerCongr` / `whiskerRightCongr`) compose. -/
theorem whiskeredVaryingWhiskerRight_conv_of_linearizeFull_eq {dim : Nat}
    {cellA cellB : CellExpr crownComputad (dim + 2)}
    {whiskerA whiskerB : CellExpr crownComputad (dim + 1)}
    (hCellA : IsAtomWord cellA) (hCellB : IsAtomWord cellB)
    (hWhiskerA : IsAtomWord whiskerA) (hWhiskerB : IsAtomWord whiskerB)
    (chainEqual : linearizeFull crownValuation (CellExpr.whiskerRight cellA whiskerA)
      = linearizeFull crownValuation (CellExpr.whiskerRight cellB whiskerB)) :
    SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad)
      (CellExpr.whiskerRight cellA whiskerA) (CellExpr.whiskerRight cellB whiskerB) := by
  have poleReduceA :
      (linearize crownValuation (boundarySource (CellExpr.whiskerRight cellA whiskerA))).coordinates
        = (linearize crownValuation whiskerA).coordinates := by
    have hzero : (linearize crownValuation (crownBaseCell (dim + 1))).coordinates
        = zeroVector (linearize crownValuation whiskerA).coordinates.length := by
      rw [linearize_length crownValuation whiskerA]
      rfl
    calc (linearize crownValuation (boundarySource (CellExpr.whiskerRight cellA whiskerA))).coordinates
        = addCoordinates (linearize crownValuation (boundarySource cellA)).coordinates
            (linearize crownValuation whiskerA).coordinates := rfl
      _ = addCoordinates (linearize crownValuation (crownBaseCell (dim + 1))).coordinates
            (linearize crownValuation whiskerA).coordinates := by rw [boundarySource_atomWord hCellA]
      _ = addCoordinates (zeroVector (linearize crownValuation whiskerA).coordinates.length)
            (linearize crownValuation whiskerA).coordinates := by rw [hzero]
      _ = (linearize crownValuation whiskerA).coordinates := addCoordinates_zeroVector_left _
  have poleReduceB :
      (linearize crownValuation (boundarySource (CellExpr.whiskerRight cellB whiskerB))).coordinates
        = (linearize crownValuation whiskerB).coordinates := by
    have hzero : (linearize crownValuation (crownBaseCell (dim + 1))).coordinates
        = zeroVector (linearize crownValuation whiskerB).coordinates.length := by
      rw [linearize_length crownValuation whiskerB]
      rfl
    calc (linearize crownValuation (boundarySource (CellExpr.whiskerRight cellB whiskerB))).coordinates
        = addCoordinates (linearize crownValuation (boundarySource cellB)).coordinates
            (linearize crownValuation whiskerB).coordinates := rfl
      _ = addCoordinates (linearize crownValuation (crownBaseCell (dim + 1))).coordinates
            (linearize crownValuation whiskerB).coordinates := by rw [boundarySource_atomWord hCellB]
      _ = addCoordinates (zeroVector (linearize crownValuation whiskerB).coordinates.length)
            (linearize crownValuation whiskerB).coordinates := by rw [hzero]
      _ = (linearize crownValuation whiskerB).coordinates := addCoordinates_zeroVector_left _
  have whiskerCoordEq : (linearize crownValuation whiskerA).coordinates
      = (linearize crownValuation whiskerB).coordinates :=
    poleReduceA.symm.trans ((linearizeFull_bsCoord_eq crownValuation chainEqual).trans poleReduceB)
  have whiskerConv : SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad) whiskerA whiskerB :=
    embedSaturatedConvOver
      (atomWord_conv_of_linearize_eq hWhiskerA hWhiskerB (congrArg SteinerCell.mk whiskerCoordEq))
  have interiorTableEq : linearize crownValuation cellA = linearize crownValuation cellB := by
    have topRow := linearizeFull_topCoord_eq crownValuation chainEqual
    exact congrArg SteinerCell.mk topRow
  have interiorConv : SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad) cellA cellB :=
    embedSaturatedConvOver (atomWord_conv_of_linearize_eq hCellA hCellB interiorTableEq)
  exact SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.whiskerRightWhiskerCongr cellA whiskerConv)
    (SaturatedConvOverWithId.whiskerRightCongr whiskerB interiorConv)

/-- ★★ **THE VARYING-WHISKER CROWN (right).**  The right-whisker dual iff. -/
theorem whiskeredVaryingWhiskerRight_conv_iff_linearizeFull_eq {dim : Nat}
    {cellA cellB : CellExpr crownComputad (dim + 2)}
    {whiskerA whiskerB : CellExpr crownComputad (dim + 1)}
    (hCellA : IsAtomWord cellA) (hCellB : IsAtomWord cellB)
    (hWhiskerA : IsAtomWord whiskerA) (hWhiskerB : IsAtomWord whiskerB) :
    SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad)
        (CellExpr.whiskerRight cellA whiskerA) (CellExpr.whiskerRight cellB whiskerB)
      ↔ linearizeFull crownValuation (CellExpr.whiskerRight cellA whiskerA)
          = linearizeFull crownValuation (CellExpr.whiskerRight cellB whiskerB) :=
  ⟨fun conv => linearizeFull_eq_of_saturatedConvWithId crownValuation conv,
   whiskeredVaryingWhiskerRight_conv_of_linearizeFull_eq hCellA hCellB hWhiskerA hWhiskerB⟩

/-! ## Non-vacuity — genuine varying-whisker verdicts over a real computad -/

/-- ★ **Positive varying-whisker verdict.**  A genuinely-varying whisker (`dimTwoWordRight` vs
`dimTwoWordLeft`, differently-associated 3-atom words) over a genuinely-varying interior (`word3Right` vs
`word3Left`) yields a REAL `SaturatedConvOverWithId` derivation — the reconstruct, not merely equal tables. -/
theorem varyingWhisker_word_conv_withId :
    SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad)
      (CellExpr.whiskerLeft dimTwoWordRight word3Right)
      (CellExpr.whiskerLeft dimTwoWordLeft word3Left) :=
  whiskeredVaryingWhisker_conv_of_linearizeFull_eq
    dimTwoWordRight_isAtomWord dimTwoWordLeft_isAtomWord
    word3Right_isAtomWord word3Left_isAtomWord (by decide)

/-- ★ **Negative varying-whisker verdict.**  Whiskers of unequal atom count (3 vs 2) are genuinely
NON-convertible under the sibling — the source pole separates them. -/
theorem varyingWhisker_word_not_conv_withId :
    ¬ SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad)
        (CellExpr.whiskerLeft dimTwoWordRight word3Right)
        (CellExpr.whiskerLeft dimTwoWordTwo word3Right) :=
  not_conv_of_linearizeFull_ne_withId crownValuation (by decide)

/-! ## OMEGA-3 r3 marker (B3 — strictly factual) -/

/-- ★ **B1/B3 — the VARYING-whisker map-IN reconstruct is SHIPPED.**  On the crown atom-word fragment,
sibling convertibility IS whiskered chain-table equality both ways even when the WHISKERING 1-cell varies
(`whiskeredVaryingWhisker_conv_iff_linearizeFull_eq` + the right dual), via the source-pole whisker read-off
and the r2 whiskering-1-cell congruences.  This closes the r2 `fxOmega3_generalWhiskeredMapInOpenR2` /
`fxOmega_generalWhiskeredCompletenessWithIdOpenR2` open work on the crown fragment.  `= true`. -/
def fxOmega3_varyingWhiskerReconstructShippedR3 : Bool := true

end FX1Poly.Polygraph.Omega
