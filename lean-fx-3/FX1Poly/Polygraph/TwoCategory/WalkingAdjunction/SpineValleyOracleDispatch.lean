import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCommuteProducerLeft

/-! # mode-3 keystone — Piece I oracle dispatch: the total `CellDescentStepOracle` modulo ONE residual

The COMMUTE producer is now closed for BOTH window directions (`commuteCellDescentStepRight` /
`commuteCellDescentStepLeft`), and the classifier is total on the two real kinds (the
`orientationExcludedBothLegs` case is proven impossible for a genuine cup·cap pair).  This file assembles the
per-step `CellDescentStepOracle` DISPATCH: for any non-valley cell, locate the innermost cup·cap redex, classify
it, and route it — COMMUTE (both directions) is DISCHARGED here; the residual STRAIGHTEN (`zigZagSharedLeg`)
kind is threaded as a single named input `CellStraightenStepInput`.  Net effect: the oracle's open surface
collapses from {excluded, commute-L, commute-R, straighten} to exactly {straighten}.

  * ★ **`LocatedCupThenCap` / `locateCupThenCap_of_not_valley`** — the Type-valued locate.  The shipped locate
    (`hasAdjacentCupThenCap_of_not_valley` / `hasAdjacentCupThenCap_split`) is Prop-valued; the dispatch produces
    a `CellDescentResult` (a `Type`, carrying the `next` cell), so the located split must be DATA, not a Prop
    `∃`.  A structural list recursion (on the spine, guided by the `Bool` valley/cup checks) produces the split
    components plus the cup/cap tags as a structure.
  * ★ **`CellStraightenStepInput`** — the residual STRAIGHTEN move, stated as an input with the producer
    signature shape for the `zigZagSharedLeg` kind.  It stays open because it needs the collapse witness
    `cupFrame ⊟ capFrame ≈ id` that window-distance-1 does NOT supply for a shared-leg NON-partner crossing
    (coupled to Piece II's non-crossing partner discipline).
  * ★ **`valleyCellDescentStepOracle`** — the total dispatch: locate, classify, `absurd` the excluded case,
    route COMMUTE by `Nat.le_total` on the two left-context widths (right/left producer), hand STRAIGHTEN to the
    input.  A `CellStraightenStepInput → CellDescentStepOracle`.
  * ★ **`matchingReductsShareSpineTrace_of_straighten_of_valleyTraceEquiv`** — the sharpened reduction:
    `MatchingReductsShareSpineTrace` now follows from `CellStraightenStepInput` ∧ `CellValleyTraceEquiv` (the
    oracle argument of `matchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv` is supplied by the
    dispatch).  The oracle is no longer an open input — only STRAIGHTEN and Piece II's cell-level trace-equiv
    remain.

## What this does NOT close (gates stay `false`)

The COMMUTE half of the oracle is fully DISCHARGED, but `CellStraightenStepInput` is a genuine residual (the
STRAIGHTEN partner-collapse — a fresh spine-frame ↔ arc-partner lift, NOT dissolved by the closed Piece II), and
`CellValleyTraceEquiv` (the cell-level Piece II block extractor) is still owed.  So a CLOSED
`CellDescentStepOracle` is NOT inhabited, and `MatchingReductsShareSpineTrace`, `convOfMapEq`, and the fib-3 gate
flags stay `false`.  This file removes the COMMUTE branches from the oracle's open surface and isolates the
residual to `CellStraightenStepInput` ∧ `CellValleyTraceEquiv`.

Raw Lean 4 + Init; the locate is structural list recursion, the dispatch is a classifier match with `absurd` +
`Nat.le_total`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

universe u

namespace FX1Poly.Polygraph

/-! ## The Type-valued locate -/

/-- A located cup-then-cap redex, carried as DATA (a structure, not a Prop `∃`): the split of the list around an
adjacent cup·cap pair plus the two tags.  The Type-valued analogue of `HasAdjacentCupThenCap` +
`hasAdjacentCupThenCap_split`, needed because the dispatch produces a `CellDescentResult` (a `Type`). -/
structure LocatedCupThenCap {α : Type u} (isCup : α → Bool) (list : List α) : Type u where
  /-- The atoms before the located pair. -/
  prefixCells : List α
  /-- The located cup. -/
  cupAtom : α
  /-- The located cap. -/
  capAtom : α
  /-- The atoms after the located pair. -/
  rest : List α
  /-- The list splits around the located pair. -/
  splitEq : list = prefixCells ++ cupAtom :: capAtom :: rest
  /-- The first located atom is a cup. -/
  isCupCup : isCup cupAtom = true
  /-- The second located atom is a cap. -/
  isCapCap : isCup capAtom = false

/-- Type-valued: a cup head with a not-all-cups tail locates a cup·cap redex.  Mirror of the Prop
`hasAdjacentCupThenCap_of_cup_of_not_allCups`, structural on the tail. -/
def locateCupThenCap_of_cup_of_not_allCups {α : Type u} (isCup : α → Bool) :
    ∀ {rest : List α}, allCups isCup rest = false →
      ∀ {cupHead : α}, isCup cupHead = true → LocatedCupThenCap isCup (cupHead :: rest)
  | [], tailNotAllCups, _, _ => by
      dsimp only [allCups] at tailNotAllCups
      exact Bool.noConfusion tailNotAllCups
  | nextAtom :: rest, tailNotAllCups, cupHead, isCupHead =>
      match isCupNext : isCup nextAtom with
      | false => ⟨[], cupHead, nextAtom, rest, rfl, isCupHead, isCupNext⟩
      | true =>
          let subLocated := locateCupThenCap_of_cup_of_not_allCups isCup
            (by
              dsimp only [allCups] at tailNotAllCups
              rw [isCupNext, Bool.true_and] at tailNotAllCups
              exact tailNotAllCups)
            isCupNext
          ⟨cupHead :: subLocated.prefixCells, subLocated.cupAtom, subLocated.capAtom,
            subLocated.rest, congrArg (cupHead :: ·) subLocated.splitEq,
            subLocated.isCupCup, subLocated.isCapCap⟩

/-- ★ **The Type-valued valley locate.**  A tag list that is NOT a cap-block-then-cup-block valley locates an
adjacent cup·cap redex AS DATA.  Mirror of the Prop `hasAdjacentCupThenCap_of_not_valley`, structural on the
list — the dispatch needs the split as a `Type`-valued structure to build the `CellDescentResult`. -/
def locateCupThenCap_of_not_valley {α : Type u} (isCup : α → Bool) :
    ∀ {list : List α}, isCapThenCupValley isCup list = false → LocatedCupThenCap isCup list
  | [], notValley => by
      dsimp only [isCapThenCupValley] at notValley
      exact Bool.noConfusion notValley
  | atom :: rest, notValley =>
      match isCupHead : isCup atom with
      | true =>
          locateCupThenCap_of_cup_of_not_allCups isCup
            (by
              dsimp only [isCapThenCupValley] at notValley
              rw [isCupHead] at notValley
              exact notValley)
            isCupHead
      | false =>
          let subLocated := locateCupThenCap_of_not_valley isCup
            (by
              dsimp only [isCapThenCupValley] at notValley
              rw [isCupHead] at notValley
              exact notValley)
          ⟨atom :: subLocated.prefixCells, subLocated.cupAtom, subLocated.capAtom,
            subLocated.rest, congrArg (atom :: ·) subLocated.splitEq,
            subLocated.isCupCup, subLocated.isCapCap⟩

/-- The spine specialization of the Type-valued locate. -/
def locateCupThenCapSpine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {spine : List (SpineAtom signature sourceMode targetMode)}
    (notValley : isCapThenCupValley SpineAtom.isCupAtom spine = false) :
    LocatedCupThenCap SpineAtom.isCupAtom spine :=
  locateCupThenCap_of_not_valley SpineAtom.isCupAtom notValley

/-! ## The residual STRAIGHTEN input -/

/-- The residual STRAIGHTEN move — the one genuinely-open per-step input after the COMMUTE half is discharged.
For a located cup·cap redex classified `zigZagSharedLeg`, produce a `CellDescentResult`.  Un-shipped: it needs
the collapse witness `cupFrame ⊟ capFrame ≈ id` that window-distance-1 does NOT supply for a shared-leg
non-partner crossing (coupled to Piece II's non-crossing partner discipline lifted to the cell level). -/
def CellStraightenStepInput : Type :=
  ∀ {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjunctionModeSignature sourceMode targetMode},
    cupAtom.isCupAtom = true → capAtom.isCupAtom = false →
    cell.spine = prefixCells ++ cupAtom :: capAtom :: rest →
    classifyAdjacentAtoms cupAtom capAtom = AdjacentCupCapKind.zigZagSharedLeg →
    CellDescentResult cell

/-! ## The total dispatch -/

/-- ★ **The total per-step oracle dispatch, modulo the STRAIGHTEN residual.**  Given the STRAIGHTEN input, for
any non-valley cell: locate the innermost cup·cap redex (`locateCupThenCapSpine`), classify it, and route:
`orientationExcludedBothLegs` is refuted (`classifyAdjacentAtoms_ne_orientationExcluded`), `zigZagSharedLeg` is
handed to the input, `disjointWindows` is COMMUTE — the right/left producer selected by `Nat.le_total` on the two
left-context widths.  The COMMUTE half is fully DISCHARGED here; only `CellStraightenStepInput` remains open. -/
def valleyCellDescentStepOracle (straighten : CellStraightenStepInput) : CellDescentStepOracle :=
  fun cell notValley =>
    let located := locateCupThenCapSpine (spine := cell.spine) notValley
    match hVerdict : classifyAdjacentAtoms located.cupAtom located.capAtom with
    | .orientationExcludedBothLegs =>
        absurd hVerdict
          (classifyAdjacentAtoms_ne_orientationExcluded located.cupAtom located.capAtom
            located.isCupCup located.isCapCap)
    | .zigZagSharedLeg =>
        straighten cell located.prefixCells located.rest located.isCupCup located.isCapCap
          located.splitEq hVerdict
    | .disjointWindows =>
        if hOffsetLe :
            located.cupAtom.leftContext.length ≤ located.capAtom.leftContext.length then
          commuteCellDescentStepRight cell located.prefixCells located.rest
            located.isCupCup located.isCapCap located.splitEq hOffsetLe hVerdict
        else
          commuteCellDescentStepLeft cell located.prefixCells located.rest
            located.isCupCup located.isCapCap located.splitEq
            ((Nat.le_total located.cupAtom.leftContext.length
              located.capAtom.leftContext.length).resolve_left hOffsetLe) hVerdict

/-! ## The sharpened reduction -/

/-- ★ **The sharpened reduction of `MatchingReductsShareSpineTrace`.**  Because the dispatch supplies the oracle
argument, `MatchingReductsShareSpineTrace` now follows from the STRAIGHTEN input AND the cell-level Piece II
trace-equivalence — the whole COMMUTE half of the oracle is consumed.  Composes
`valleyCellDescentStepOracle` into `matchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv`. -/
theorem matchingReductsShareSpineTrace_of_straighten_of_valleyTraceEquiv
    (straighten : CellStraightenStepInput) (valleyTraceEquiv : CellValleyTraceEquiv) :
    MatchingReductsShareSpineTrace :=
  matchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv
    (valleyCellDescentStepOracle straighten) valleyTraceEquiv

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the COMMUTE half of the per-step oracle is fully DISCHARGED; the oracle's open surface is
collapsed to ONE residual.**  `locateCupThenCap_of_not_valley` produces the located cup·cap redex as `Type`-valued
DATA (the Prop locate cannot feed the `Type`-valued `CellDescentResult`); `valleyCellDescentStepOracle` classifies
it and routes — the excluded case refuted, both COMMUTE directions discharged via the two producers selected by
`Nat.le_total`, the STRAIGHTEN case threaded as the single input `CellStraightenStepInput`.  So
`MatchingReductsShareSpineTrace` reduces to `CellStraightenStepInput` ∧ `CellValleyTraceEquiv`
(`matchingReductsShareSpineTrace_of_straighten_of_valleyTraceEquiv`) — the oracle is no longer an open input.

  What this marker does NOT close: `CellStraightenStepInput` (the STRAIGHTEN partner-collapse — a fresh
  spine-frame ↔ arc-partner lift supplying `cupFrame ⊟ capFrame ≈ id`, NOT dissolved by the closed Piece II) and
  `CellValleyTraceEquiv` (the cell-level Piece II block extractor).  Both are genuinely open, so a CLOSED
  `CellDescentStepOracle` is NOT inhabited: `convOfMapEq`, the keystone `SaturatedMatchingCanonicalization`, and
  the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyOracleDispatch : Bool := true

end FX1Poly.Polygraph
