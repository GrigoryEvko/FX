import FX1Poly.Polygraph.Omega.ZXPhaseFree.SpiderResidual

/-! # Polygraph/Omega/ZXPhaseFree/SpiderTailDeath — the closed-form absorbed rows
and the completeness-sharpened spider tail-death walls

The r15 `SpiderResidual` reduced each phase-free spider residual
(`zxbZSpiderAbsorbStatement` / `zxbXSpiderAbsorbStatement`) to exactly one named
existential, the tail-death `zxsZSpiderTailDeathStatement` /
`zxsXSpiderTailDeathStatement`: a whiskered spider above the generator-block/kill
core absorbs into SOME generator list on the exit boundary.  The r15 wall note
framed the remaining death as a subspace-intersection Gaussian elimination with no
per-row fold.  This round pins down WHAT the absorbed rows are and reframes the
wall as a pure completeness obligation.

* (i)   THE CLOSED-FORM ABSORBED ROWS (`zxdAbsorbedRowsZ` / `zxdAbsorbedRowsX`):
  the existential witness is SOLVED in closed form.  For the whiskered-spider core
  of shape `exitWidth + codWidth -> codWidth`, the absorbed rows are the fold of
  the core's own generator matrix that XORs the codomain band back into the input
  codomain band (`zxdFoldRows`).  The fold preserves width (`zxdFoldRowsWidth`), so
  the existential's width side-condition is discharged mechanically.  This removes
  ALL mystery about the absorbed rows: they are an explicit function of the input.

* (ii)  THE WIDTH-CHANGING JOINT PINS (`zxdZClosedFormSpanPinBands` /
  `...Merge` / `zxdXClosedFormSpanPinBands`, plus the two content instances): the
  closed-form absorbed rows are kernel-verified span-correct at configurations
  jointly exercising nonzero side bands, a multi-row generator list, a codomain
  wire band, AND a genuine width change (`topLegCount != botLegCount`, both
  directions, both colours).

* (iii) THE SHARPENED WALLS (owner false), `zxdZSpiderTailDeathClosedFormConv` /
  `zxdXSpiderTailDeathClosedFormConv`: with the existential discharged, only the
  conversion of two concrete diagrams remains — the whiskered-spider core versus
  the killed core of the closed-form absorbed rows.  The reductions
  `zxdZTailDeathOfClosedForm` / `zxdXTailDeathOfClosedForm` prove that these
  conversions imply the r15 tail-deaths, and `zxdZSpiderResidualOfClosedForm` /
  `zxdXSpiderResidualOfClosedForm` chain them all the way to the residuals.

* (iv)  THE DEEPER WALL, NAMED (`zxdConvOfSpanReflection`): the closed-form
  conversion is exactly an instance of the GLOBAL completeness-reflection
  principle `zpSpanEqB = true -> ZxwConv`, the converse of the committed soundness
  bridge `zxwConvSpanEqB`.  The demonstration `zxdZClosedFormConvOfReflectionAtContentInstance`
  shows that reflection discharges a content instance from its rfl-checkable span
  pin, making the missing lemma concrete.

WALL NOTE (two burned attacks, this round's own, concretely certified):

* (a) NO PER-ROW / PER-BLOCK FOLD OF THE GENERATOR LIST.  Absorption depends
  GLOBALLY on the whole generator set through the kill:
  `zxdZAbsorptionIsGlobalNotPerRow` certifies that the two differing-bit rows
  `[true,false]` and `[false,true]` TOGETHER free the spider input (absorbed span
  dimension 1) whereas EACH row alone kills it (absorbed span the zero subspace).
  No fold over the generator rows can reproduce this non-additive collapse — the
  induction-on-generator-rows / per-block spider ride is dead.

* (b) NO COMPLETENESS REFLECTION.  The tail-death's span equality is kernel-TRUE
  at every pin, yet the library exposes only the one-directional soundness bridge
  `zxwConvSpanEqB : ZxwConv -> spanEqB = true`.  There is NO `spanEqB = true ->
  ZxwConv` lemma — that IS the global completeness theorem the whole normal-form
  program is proving.  The refutation `zxdSpiderRideWrongRowsNotConv` witnesses
  that a wrong absorbed-row choice genuinely separates, so the conversion carries
  content and cannot be waved through.

The bridge from `zxdConvOfSpanReflection` to the closed-form conversions is the
generic denotational soundness of the fold (span of the killed core of the closed
form equals span of the whiskered-spider core), TRUE at all six pins and the next
round's tractable, completeness-free target.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`,
no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive
scrutinees.  The committed owner-false flags in `AbsorptionInduction`,
`CrossingResidual`, and `SpiderResidual` stay byte-intact; the fresh true content
marker is `zxdHasClosedFormAbsorbedRows`; the fresh owner-false walls are
`zxdZSpiderTailDeathClosedFormConvIsProven`,
`zxdXSpiderTailDeathClosedFormConvIsProven`, and
`zxdConvOfSpanReflectionIsProven`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — the closed-form fold: the absorbed-rows constructor

A generator row of the whiskered-spider core has the shape `keep(keepWidth) ++
cin(bandWidth) ++ out(bandWidth)` (input `keep ++ cin`, output `out`).  Folding
the output band back into the input band produces the absorbed row `keep ++ (cin
xor out)`.  All plumbing is structural cons-recursion; no `List.append`, no
`Nat.sub`. -/

/-- Cons-only row concatenation (fresh, to stay off `List.append`). -/
def zxdCatRow : List Bool -> List Bool -> List Bool
  | [], secondBits => secondBits
  | headBit :: tailBits, secondBits => headBit :: zxdCatRow tailBits secondBits

theorem zxdCatRowLength : (firstBits secondBits : List Bool) ->
    (zxdCatRow firstBits secondBits).length = firstBits.length + secondBits.length
  | [], secondBits => by
      show secondBits.length = ([] : List Bool).length + secondBits.length
      rw [show ([] : List Bool).length = 0 from rfl, Nat.zero_add]
  | headBit :: tailBits, secondBits => by
      show (zxdCatRow tailBits secondBits).length + 1
        = (headBit :: tailBits).length + secondBits.length
      rw [zxdCatRowLength tailBits secondBits,
        show (headBit :: tailBits).length = tailBits.length + 1 from rfl, Nat.succ_add]

/-- Split a row into its first `splitCount` bits and the remainder. -/
def zxdSplitAt : Nat -> List Bool -> (List Bool × List Bool)
  | 0, bits => ([], bits)
  | _splitPred + 1, [] => ([], [])
  | splitPred + 1, headBit :: tailBits =>
      (headBit :: (zxdSplitAt splitPred tailBits).fst, (zxdSplitAt splitPred tailBits).snd)

theorem zxdSplitAtPrefixLength : (splitCount remainderCount : Nat) -> (bits : List Bool) ->
    bits.length = splitCount + remainderCount ->
    (zxdSplitAt splitCount bits).fst.length = splitCount
  | 0, _remainderCount, _bits, _hLen => rfl
  | splitPred + 1, remainderCount, [], hLen => by
      rw [show ([] : List Bool).length = 0 from rfl, Nat.succ_add] at hLen
      exact Nat.noConfusion hLen
  | splitPred + 1, remainderCount, headBit :: tailBits, hLen => by
      show ((zxdSplitAt splitPred tailBits).fst).length + 1 = splitPred + 1
      have hTail : tailBits.length = splitPred + remainderCount := by
        rw [show (headBit :: tailBits).length = tailBits.length + 1 from rfl, Nat.succ_add]
          at hLen
        exact Nat.succ.inj hLen
      rw [zxdSplitAtPrefixLength splitPred remainderCount tailBits hTail]

theorem zxdSplitAtSuffixLength : (splitCount remainderCount : Nat) -> (bits : List Bool) ->
    bits.length = splitCount + remainderCount ->
    (zxdSplitAt splitCount bits).snd.length = remainderCount
  | 0, remainderCount, bits, hLen => by
      show bits.length = remainderCount
      rw [hLen, Nat.zero_add]
  | splitPred + 1, remainderCount, [], hLen => by
      rw [show ([] : List Bool).length = 0 from rfl, Nat.succ_add] at hLen
      exact Nat.noConfusion hLen
  | splitPred + 1, remainderCount, headBit :: tailBits, hLen => by
      show (zxdSplitAt splitPred tailBits).snd.length = remainderCount
      have hTail : tailBits.length = splitPred + remainderCount := by
        rw [show (headBit :: tailBits).length = tailBits.length + 1 from rfl, Nat.succ_add]
          at hLen
        exact Nat.succ.inj hLen
      exact zxdSplitAtSuffixLength splitPred remainderCount tailBits hTail

/-- THE FOLD: keep the first `keepWidth` bits, XOR the two `bandWidth`-halves of
the remaining `2 * bandWidth` bits.  On a core generator row `keep ++ cin ++ out`
this yields the absorbed row `keep ++ (cin xor out)`. -/
def zxdFoldRow (keepWidth bandWidth : Nat) (row : List Bool) : List Bool :=
  zxdCatRow (zxdSplitAt keepWidth row).fst
    (zxpRowXor (zxdSplitAt bandWidth (zxdSplitAt keepWidth row).snd).fst
      (zxdSplitAt bandWidth (zxdSplitAt keepWidth row).snd).snd)

theorem zxdFoldRowLength (keepWidth bandWidth : Nat) (row : List Bool)
    (hLen : row.length = (keepWidth + bandWidth) + bandWidth) :
    (zxdFoldRow keepWidth bandWidth row).length = keepWidth + bandWidth := by
  show (zxdCatRow (zxdSplitAt keepWidth row).fst
      (zxpRowXor (zxdSplitAt bandWidth (zxdSplitAt keepWidth row).snd).fst
        (zxdSplitAt bandWidth (zxdSplitAt keepWidth row).snd).snd)).length
    = keepWidth + bandWidth
  have hRowSplit : row.length = keepWidth + (bandWidth + bandWidth) := by
    rw [hLen, Nat.add_assoc]
  have hHeadLen : (zxdSplitAt keepWidth row).fst.length = keepWidth :=
    zxdSplitAtPrefixLength keepWidth (bandWidth + bandWidth) row hRowSplit
  have hTailLen : (zxdSplitAt keepWidth row).snd.length = bandWidth + bandWidth :=
    zxdSplitAtSuffixLength keepWidth (bandWidth + bandWidth) row hRowSplit
  have hCinLen : (zxdSplitAt bandWidth (zxdSplitAt keepWidth row).snd).fst.length = bandWidth :=
    zxdSplitAtPrefixLength bandWidth bandWidth (zxdSplitAt keepWidth row).snd hTailLen
  have hOutLen : (zxdSplitAt bandWidth (zxdSplitAt keepWidth row).snd).snd.length = bandWidth :=
    zxdSplitAtSuffixLength bandWidth bandWidth (zxdSplitAt keepWidth row).snd hTailLen
  rw [zxdCatRowLength, hHeadLen, zxpRowXorLength _ _ bandWidth hCinLen hOutLen]

/-- The fold applied to every generator row of a matrix. -/
def zxdFoldRows (keepWidth bandWidth : Nat) : List (List Bool) -> List (List Bool)
  | [] => []
  | row :: restRows => zxdFoldRow keepWidth bandWidth row :: zxdFoldRows keepWidth bandWidth restRows

theorem zxdFoldRowsWidth (keepWidth bandWidth : Nat) : (rows : List (List Bool)) ->
    ZxpAllWidth ((keepWidth + bandWidth) + bandWidth) rows ->
    ZxpAllWidth (keepWidth + bandWidth) (zxdFoldRows keepWidth bandWidth rows)
  | [], _hAll => ZxpAllWidth.nil
  | row :: restRows, hAll => by
      cases hAll with
      | cons hHead hRest =>
          exact ZxpAllWidth.cons (zxdFoldRowLength keepWidth bandWidth row hHead)
            (zxdFoldRowsWidth keepWidth bandWidth restRows hRest)

/-! ## Stage 1 — the core diagrams and the closed-form absorbed rows -/

/-- The whiskered-spider core (init already peeled): a whiskered Z-spider above the
generator-block/kill core, exactly the LHS of `zxsZSpiderTailDeathStatement`. -/
def zxdSpiderTailCoreZ (topLegCount botLegCount leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool)) : ZxpDiagram :=
  { sourceArity := (leftWires + (topLegCount + rightWires)) + codWidth
    layers := zxpWhiskerLayer leftWires (rightWires + codWidth)
        [ZxpCell.zSpider topLegCount botLegCount]
      :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
          [zxnKillLayer (leftWires + (botLegCount + rightWires)) codWidth] }

/-- The whiskered-spider core for the X colour. -/
def zxdSpiderTailCoreX (topLegCount botLegCount leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool)) : ZxpDiagram :=
  { sourceArity := (leftWires + (topLegCount + rightWires)) + codWidth
    layers := zxpWhiskerLayer leftWires (rightWires + codWidth)
        [ZxpCell.xSpider topLegCount botLegCount]
      :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
          [zxnKillLayer (leftWires + (botLegCount + rightWires)) codWidth] }

/-- The killed core of some absorbed rows on the exit boundary, exactly the RHS of
the tail-death statement. -/
def zxdKilledCore (topLegCount leftWires rightWires codWidth : Nat)
    (absorbedRows : List (List Bool)) : ZxpDiagram :=
  { sourceArity := (leftWires + (topLegCount + rightWires)) + codWidth
    layers := zxpCatLayers (zxnGeneratorBlockLayers absorbedRows)
        [zxnKillLayer (leftWires + (topLegCount + rightWires)) codWidth] }

/-- THE CLOSED-FORM Z ABSORBED ROWS: the fold of the whiskered-spider core's own
generator matrix.  Keep the `leftWires + (topLegCount + rightWires)` boundary
strands, XOR the codomain band into the input codomain band. -/
def zxdAbsorbedRowsZ (topLegCount botLegCount leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool)) : List (List Bool) :=
  zxdFoldRows (leftWires + (topLegCount + rightWires)) codWidth
    (zxpDiagramDenote (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth
      generatorRows))

/-- THE CLOSED-FORM X ABSORBED ROWS: the colour mirror. -/
def zxdAbsorbedRowsX (topLegCount botLegCount leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool)) : List (List Bool) :=
  zxdFoldRows (leftWires + (topLegCount + rightWires)) codWidth
    (zxpDiagramDenote (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth
      generatorRows))

/-- The four-summand associativity bridge used to reconcile whisker arities with
the declared boundary widths. -/
theorem zxdAssocBridge (firstWidth secondWidth thirdWidth fourthWidth : Nat) :
    (firstWidth + (secondWidth + thirdWidth)) + fourthWidth
      = firstWidth + (secondWidth + (thirdWidth + fourthWidth)) := by
  rw [Nat.add_assoc firstWidth (secondWidth + thirdWidth) fourthWidth,
    Nat.add_assoc secondWidth thirdWidth fourthWidth]

/-- The Z core is well-formed. -/
theorem zxdSpiderTailCoreZWF (topLegCount botLegCount leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth ((leftWires + (botLegCount + rightWires)) + codWidth) generatorRows) :
    ZxpDiagramWF (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth
      generatorRows) := by
  refine ZxpLayersWF.cons ?_ ?_
  · rw [zxpWhiskerLayerDomArity,
      show zxpLayerDomArity [ZxpCell.zSpider topLegCount botLegCount] = topLegCount from by
        show zxpCellDomArity (ZxpCell.zSpider topLegCount botLegCount) + 0 = topLegCount
        rw [Nat.add_zero]; rfl]
    exact (zxdAssocBridge leftWires topLegCount rightWires codWidth).symm
  · rw [zxpWhiskerLayerCodArity,
      show zxpLayerCodArity [ZxpCell.zSpider topLegCount botLegCount] = botLegCount from by
        show zxpCellCodArity (ZxpCell.zSpider topLegCount botLegCount) + 0 = botLegCount
        rw [Nat.add_zero]; rfl]
    have hCast : ZxpAllWidth (leftWires + (botLegCount + (rightWires + codWidth))) generatorRows :=
      zxpAllWidthCast (zxdAssocBridge leftWires botLegCount rightWires codWidth) hAll
    refine zxpLayersWFCat (zxnGeneratorBlockLayers generatorRows)
      [zxnKillLayer (leftWires + (botLegCount + rightWires)) codWidth]
      (zxnGeneratorBlockLayersWF generatorRows
        (leftWires + (botLegCount + (rightWires + codWidth))) hCast) ?_
    rw [zxnGeneratorBlockLayersCodArity generatorRows
      (leftWires + (botLegCount + (rightWires + codWidth))) hCast]
    refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
    rw [zxnKillLayerDomArity]
    exact zxdAssocBridge leftWires botLegCount rightWires codWidth

/-- The Z core's codomain arity is `codWidth`. -/
theorem zxdSpiderTailCoreZCod (topLegCount botLegCount leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth ((leftWires + (botLegCount + rightWires)) + codWidth) generatorRows) :
    zxpDiagramCodArity (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth
      generatorRows) = codWidth := by
  show zxpLayersCodArity
      (zxpLayerCodArity (zxpWhiskerLayer leftWires (rightWires + codWidth)
        [ZxpCell.zSpider topLegCount botLegCount]))
      (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
          [zxnKillLayer (leftWires + (botLegCount + rightWires)) codWidth]) = codWidth
  rw [zxpWhiskerLayerCodArity,
    show zxpLayerCodArity [ZxpCell.zSpider topLegCount botLegCount] = botLegCount from by
      show zxpCellCodArity (ZxpCell.zSpider topLegCount botLegCount) + 0 = botLegCount
      rw [Nat.add_zero]; rfl]
  have hCast : ZxpAllWidth (leftWires + (botLegCount + (rightWires + codWidth))) generatorRows :=
    zxpAllWidthCast (zxdAssocBridge leftWires botLegCount rightWires codWidth) hAll
  rw [zxpLayersCodArityCat,
    zxnGeneratorBlockLayersCodArity generatorRows
      (leftWires + (botLegCount + (rightWires + codWidth))) hCast]
  exact zxnKillLayerCodArity (leftWires + (botLegCount + rightWires)) codWidth

/-- The X core is well-formed (colour mirror). -/
theorem zxdSpiderTailCoreXWF (topLegCount botLegCount leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth ((leftWires + (botLegCount + rightWires)) + codWidth) generatorRows) :
    ZxpDiagramWF (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth
      generatorRows) := by
  refine ZxpLayersWF.cons ?_ ?_
  · rw [zxpWhiskerLayerDomArity,
      show zxpLayerDomArity [ZxpCell.xSpider topLegCount botLegCount] = topLegCount from by
        show zxpCellDomArity (ZxpCell.xSpider topLegCount botLegCount) + 0 = topLegCount
        rw [Nat.add_zero]; rfl]
    exact (zxdAssocBridge leftWires topLegCount rightWires codWidth).symm
  · rw [zxpWhiskerLayerCodArity,
      show zxpLayerCodArity [ZxpCell.xSpider topLegCount botLegCount] = botLegCount from by
        show zxpCellCodArity (ZxpCell.xSpider topLegCount botLegCount) + 0 = botLegCount
        rw [Nat.add_zero]; rfl]
    have hCast : ZxpAllWidth (leftWires + (botLegCount + (rightWires + codWidth))) generatorRows :=
      zxpAllWidthCast (zxdAssocBridge leftWires botLegCount rightWires codWidth) hAll
    refine zxpLayersWFCat (zxnGeneratorBlockLayers generatorRows)
      [zxnKillLayer (leftWires + (botLegCount + rightWires)) codWidth]
      (zxnGeneratorBlockLayersWF generatorRows
        (leftWires + (botLegCount + (rightWires + codWidth))) hCast) ?_
    rw [zxnGeneratorBlockLayersCodArity generatorRows
      (leftWires + (botLegCount + (rightWires + codWidth))) hCast]
    refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
    rw [zxnKillLayerDomArity]
    exact zxdAssocBridge leftWires botLegCount rightWires codWidth

/-- The X core's codomain arity is `codWidth` (colour mirror). -/
theorem zxdSpiderTailCoreXCod (topLegCount botLegCount leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth ((leftWires + (botLegCount + rightWires)) + codWidth) generatorRows) :
    zxpDiagramCodArity (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth
      generatorRows) = codWidth := by
  show zxpLayersCodArity
      (zxpLayerCodArity (zxpWhiskerLayer leftWires (rightWires + codWidth)
        [ZxpCell.xSpider topLegCount botLegCount]))
      (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
          [zxnKillLayer (leftWires + (botLegCount + rightWires)) codWidth]) = codWidth
  rw [zxpWhiskerLayerCodArity,
    show zxpLayerCodArity [ZxpCell.xSpider topLegCount botLegCount] = botLegCount from by
      show zxpCellCodArity (ZxpCell.xSpider topLegCount botLegCount) + 0 = botLegCount
      rw [Nat.add_zero]; rfl]
  have hCast : ZxpAllWidth (leftWires + (botLegCount + (rightWires + codWidth))) generatorRows :=
    zxpAllWidthCast (zxdAssocBridge leftWires botLegCount rightWires codWidth) hAll
  rw [zxpLayersCodArityCat,
    zxnGeneratorBlockLayersCodArity generatorRows
      (leftWires + (botLegCount + (rightWires + codWidth))) hCast]
  exact zxnKillLayerCodArity (leftWires + (botLegCount + rightWires)) codWidth

/-- The closed-form Z absorbed rows have the exit-boundary width the tail-death
existential demands: the fold of the core's width-`((exit)+cod)+cod` generator
matrix has width `(exit)+cod`. -/
theorem zxdAbsorbedRowsZWidth (topLegCount botLegCount leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth ((leftWires + (botLegCount + rightWires)) + codWidth) generatorRows) :
    ZxpAllWidth ((leftWires + (topLegCount + rightWires)) + codWidth)
      (zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows) := by
  have hDenoteWidth := zxpDiagramDenoteWidth
    (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)
    (zxdSpiderTailCoreZWF topLegCount botLegCount leftWires rightWires codWidth generatorRows hAll)
  rw [zxdSpiderTailCoreZCod topLegCount botLegCount leftWires rightWires codWidth generatorRows hAll]
    at hDenoteWidth
  exact zxdFoldRowsWidth (leftWires + (topLegCount + rightWires)) codWidth
    (zxpDiagramDenote (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth
      generatorRows)) hDenoteWidth

/-- The closed-form X absorbed rows have the exit-boundary width (colour mirror). -/
theorem zxdAbsorbedRowsXWidth (topLegCount botLegCount leftWires rightWires codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth ((leftWires + (botLegCount + rightWires)) + codWidth) generatorRows) :
    ZxpAllWidth ((leftWires + (topLegCount + rightWires)) + codWidth)
      (zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows) := by
  have hDenoteWidth := zxpDiagramDenoteWidth
    (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth generatorRows)
    (zxdSpiderTailCoreXWF topLegCount botLegCount leftWires rightWires codWidth generatorRows hAll)
  rw [zxdSpiderTailCoreXCod topLegCount botLegCount leftWires rightWires codWidth generatorRows hAll]
    at hDenoteWidth
  exact zxdFoldRowsWidth (leftWires + (topLegCount + rightWires)) codWidth
    (zxpDiagramDenote (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth
      generatorRows)) hDenoteWidth

/-! ## Stage 2 — the sharpened walls (existential discharged) and the reductions -/

/-- THE Z CLOSED-FORM CONVERSION (owner false): the whiskered-spider core converts
to the killed core of its CLOSED-FORM absorbed rows.  The r15 existential is
discharged; only this concrete conversion remains — a completeness obligation. -/
def zxdZSpiderTailDeathClosedFormConv : Prop :=
  (topLegCount botLegCount leftWires rightWires codWidth : Nat) ->
  (generatorRows : List (List Bool)) ->
  ZxpAllWidth ((leftWires + (botLegCount + rightWires)) + codWidth) generatorRows ->
  ZxwConv (zxdSpiderTailCoreZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)
    (zxdKilledCore topLegCount leftWires rightWires codWidth
      (zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows))

/-- THE X CLOSED-FORM CONVERSION (owner false): the colour mirror. -/
def zxdXSpiderTailDeathClosedFormConv : Prop :=
  (topLegCount botLegCount leftWires rightWires codWidth : Nat) ->
  (generatorRows : List (List Bool)) ->
  ZxpAllWidth ((leftWires + (botLegCount + rightWires)) + codWidth) generatorRows ->
  ZxwConv (zxdSpiderTailCoreX topLegCount botLegCount leftWires rightWires codWidth generatorRows)
    (zxdKilledCore topLegCount leftWires rightWires codWidth
      (zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows))

/-- THE Z SHARPENING: the closed-form conversion implies the r15 tail-death — the
explicit absorbed rows are the existential witness, their width is proven, and the
supplied conversion is the second conjunct. -/
theorem zxdZTailDeathOfClosedForm (hClosedForm : zxdZSpiderTailDeathClosedFormConv) :
    zxsZSpiderTailDeathStatement := by
  intro topLegCount botLegCount leftWires rightWires codWidth generatorRows hAll
  exact Exists.intro
    (zxdAbsorbedRowsZ topLegCount botLegCount leftWires rightWires codWidth generatorRows)
    (And.intro
      (zxdAbsorbedRowsZWidth topLegCount botLegCount leftWires rightWires codWidth generatorRows
        hAll)
      (hClosedForm topLegCount botLegCount leftWires rightWires codWidth generatorRows hAll))

/-- THE X SHARPENING: the colour mirror. -/
theorem zxdXTailDeathOfClosedForm (hClosedForm : zxdXSpiderTailDeathClosedFormConv) :
    zxsXSpiderTailDeathStatement := by
  intro topLegCount botLegCount leftWires rightWires codWidth generatorRows hAll
  exact Exists.intro
    (zxdAbsorbedRowsX topLegCount botLegCount leftWires rightWires codWidth generatorRows)
    (And.intro
      (zxdAbsorbedRowsXWidth topLegCount botLegCount leftWires rightWires codWidth generatorRows
        hAll)
      (hClosedForm topLegCount botLegCount leftWires rightWires codWidth generatorRows hAll))

/-- THE Z RESIDUAL FROM THE CLOSED FORM: chaining the sharpening through the r15
flip discharges the whole Z-spider residual from the closed-form conversion. -/
theorem zxdZSpiderResidualOfClosedForm (hClosedForm : zxdZSpiderTailDeathClosedFormConv) :
    zxbZSpiderAbsorbStatement :=
  zxsZSpiderAbsorbOfTailDeath (zxdZTailDeathOfClosedForm hClosedForm)

/-- THE X RESIDUAL FROM THE CLOSED FORM: the colour mirror. -/
theorem zxdXSpiderResidualOfClosedForm (hClosedForm : zxdXSpiderTailDeathClosedFormConv) :
    zxbXSpiderAbsorbStatement :=
  zxsXSpiderAbsorbOfTailDeath (zxdXTailDeathOfClosedForm hClosedForm)

/-! ## Stage 3 — the deeper wall: the completeness-reflection principle -/

/-- THE COMPLETENESS-REFLECTION PRINCIPLE (owner false): well-formed, same-boundary
diagrams whose generator matrices pass the mutual-reduction span decision are
wiring-extended convertible.  This is the exact converse of the committed
soundness bridge `zxwConvSpanEqB`; proving it IS phase-free completeness. -/
def zxdConvOfSpanReflection : Prop :=
  (firstDiagram secondDiagram : ZxpDiagram) ->
  zxpDiagramWFB firstDiagram = true ->
  zxpDiagramWFB secondDiagram = true ->
  firstDiagram.sourceArity = secondDiagram.sourceArity ->
  zxpDiagramCodArity firstDiagram = zxpDiagramCodArity secondDiagram ->
  zxpSpanEqB (zxpDiagramDenote firstDiagram) (zxpDiagramDenote secondDiagram) = true ->
  ZxwConv firstDiagram secondDiagram

/-- REFLECTION DISCHARGES A CONTENT INSTANCE: at the width-changing content instance
(`botLegCount = 2` down to `topLegCount = 1`), the reflection principle turns the
rfl-checkable well-formedness, boundary, and span facts into the closed-form
conversion — making the missing lemma concrete. -/
theorem zxdZClosedFormConvOfReflectionAtContentInstance
    (hReflection : zxdConvOfSpanReflection) :
    ZxwConv (zxdSpiderTailCoreZ 1 2 0 0 0 [[true, false], [false, true]])
      (zxdKilledCore 1 0 0 0 (zxdAbsorbedRowsZ 1 2 0 0 0 [[true, false], [false, true]])) :=
  hReflection _ _ rfl rfl rfl rfl rfl

/-! ## Stage 4 — the invariant-first joint pins for the closed-form absorbed rows -/

/-- Content-instance pin (Z, `2 -> 1`): the closed-form absorbed rows are span-correct
at the r15 width-changing content instance. -/
theorem zxdZClosedFormContentInstanceSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote (zxdSpiderTailCoreZ 1 2 0 0 0 [[true, false], [false, true]]))
      (zxpDiagramDenote (zxdKilledCore 1 0 0 0
        (zxdAbsorbedRowsZ 1 2 0 0 0 [[true, false], [false, true]]))) = true := rfl

/-- Joint pin (Z, `1 -> 2`, nonzero left/right/codomain bands, multi-row generator):
the closed-form absorbed rows are span-correct. -/
theorem zxdZClosedFormSpanPinBands :
    zxpSpanEqB
      (zxpDiagramDenote (zxdSpiderTailCoreZ 1 2 1 1 1
        [[true, false, false, false, false], [false, true, true, false, false]]))
      (zxpDiagramDenote (zxdKilledCore 1 1 1 1
        (zxdAbsorbedRowsZ 1 2 1 1 1
          [[true, false, false, false, false], [false, true, true, false, false]]))) = true := rfl

/-- Joint pin (Z, `2 -> 1` merge direction, left band + codomain band, multi-row):
the closed-form absorbed rows are span-correct. -/
theorem zxdZClosedFormSpanPinMerge :
    zxpSpanEqB
      (zxpDiagramDenote (zxdSpiderTailCoreZ 2 1 1 0 1 [[true, true, false], [false, false, true]]))
      (zxpDiagramDenote (zxdKilledCore 2 1 0 1
        (zxdAbsorbedRowsZ 2 1 1 0 1 [[true, true, false], [false, false, true]]))) = true := rfl

/-- Content-instance pin (X, `1 -> 2`): the colour mirror of the r15 X content
instance. -/
theorem zxdXClosedFormContentInstanceSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote (zxdSpiderTailCoreX 2 1 0 0 0 [[true]]))
      (zxpDiagramDenote (zxdKilledCore 2 0 0 0
        (zxdAbsorbedRowsX 2 1 0 0 0 [[true]]))) = true := rfl

/-- Joint pin (X, `2 -> 1`, nonzero left/right/codomain bands, multi-row generator):
the closed-form absorbed rows are span-correct. -/
theorem zxdXClosedFormSpanPinBands :
    zxpSpanEqB
      (zxpDiagramDenote (zxdSpiderTailCoreX 2 1 1 1 1
        [[true, false, false, false], [false, true, false, true]]))
      (zxpDiagramDenote (zxdKilledCore 2 1 1 1
        (zxdAbsorbedRowsX 2 1 1 1 1
          [[true, false, false, false], [false, true, false, true]]))) = true := rfl

/-! ## Stage 5 — the burned-attack certificates -/

/-- REFUTATION (the conversion carries content): a WRONG absorbed-row choice
separates.  The whiskered copy-spider core at the content instance is span-DISTINCT
from the killed core of the empty generator list, so no `ZxwConv` between them
exists — the closed-form choice is load-bearing, absorption cannot be waved
through. -/
theorem zxdSpiderRideWrongRowsNotConv :
    Not (ZxwConv (zxdSpiderTailCoreZ 1 2 0 0 0 [[true, false], [false, true]])
      (zxdKilledCore 1 0 0 0 [])) := by
  intro hConv
  have hTrue := zxwConvSpanEqB hConv
  have hFalse : zxpSpanEqB
      (zxpDiagramDenote (zxdSpiderTailCoreZ 1 2 0 0 0 [[true, false], [false, true]]))
      (zxpDiagramDenote (zxdKilledCore 1 0 0 0 [])) = false := rfl
  rw [hFalse] at hTrue
  exact Bool.noConfusion hTrue

/-- BURNED ATTACK (a): absorption is GLOBAL, not a per-row fold of the generator
list.  The two differing-bit rows TOGETHER free the spider input (absorbed span =
the one-strand full effect `[[true]]`), while EACH row alone kills it (absorbed
span = the zero subspace `[]`).  Since the one-strand full effect is span-DISTINCT
from the zero subspace, no fold over the generator rows can reproduce the
absorbed-row collapse — the induction-on-generator-rows / per-block spider ride is
impossible. -/
theorem zxdZAbsorptionIsGlobalNotPerRow :
    And (zxpSpanEqB (zxdAbsorbedRowsZ 1 2 0 0 0 [[true, false], [false, true]]) [[true]] = true)
      (And (zxpSpanEqB (zxdAbsorbedRowsZ 1 2 0 0 0 [[true, false]]) [] = true)
        (And (zxpSpanEqB (zxdAbsorbedRowsZ 1 2 0 0 0 [[false, true]]) [] = true)
          (zxpSpanEqB ([[true]] : List (List Bool)) [] = false))) :=
  And.intro rfl (And.intro rfl (And.intro rfl rfl))

/-! ## Stage 6 — the honest marker ledger -/

/-- CONTENT MARKER (TRUE): the closed-form absorbed rows are LIVE — the fold
constructor `zxdFoldRows`, its width preservation `zxdFoldRowsWidth`, the explicit
witnesses `zxdAbsorbedRowsZ` / `zxdAbsorbedRowsX` with proven exit-boundary width,
and the reductions `zxdZTailDeathOfClosedForm` / `zxdXTailDeathOfClosedForm` (and
their chains to the residuals) are machine-checked zero-axiom.  The r15 tail-death
existential is discharged: the absorbed rows are an explicit function of the input,
span-certified at six joint pins. -/
def zxdHasClosedFormAbsorbedRows : Bool := true

/-- OWNER MARKER (FALSE): the Z closed-form conversion
`zxdZSpiderTailDeathClosedFormConv` — the whiskered-spider core converting to the
killed core of its closed-form absorbed rows — is NOT proven this round; it is a
completeness obligation (see `zxdConvOfSpanReflection` and the burned attacks). -/
def zxdZSpiderTailDeathClosedFormConvIsProven : Bool := false

/-- OWNER MARKER (FALSE): the X closed-form conversion is NOT proven this round. -/
def zxdXSpiderTailDeathClosedFormConvIsProven : Bool := false

/-- OWNER MARKER (FALSE): the completeness-reflection principle
`zxdConvOfSpanReflection` (the converse of `zxwConvSpanEqB`) is NOT proven; proving
it IS phase-free completeness. -/
def zxdConvOfSpanReflectionIsProven : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
