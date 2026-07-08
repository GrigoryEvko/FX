import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCommuteProducerLeft
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenAssembly

/-! # mode-3 keystone — Piece I oracle dispatch: the CLOSED `CellDescentStepOracle`

The COMMUTE producer is closed for BOTH window directions (`commuteCellDescentStepRight` /
`commuteCellDescentStepLeft`), the classifier is total on the two real kinds (the `orientationExcludedBothLegs`
case is proven impossible for a genuine cup·cap pair), and — via the STRAIGHTEN assembly `straightenCellDescentStep`
(`SpineValleyStraightenAssembly`, dispatching both handednesses by the width dichotomy) — the STRAIGHTEN move is
now DISCHARGED with no input.  This file assembles the per-step `CellDescentStepOracle` DISPATCH: for any non-valley
cell, locate the innermost cup·cap redex, classify it, and route it — every branch is closed.  Net effect: the
oracle's open surface collapses from {excluded, commute-L, commute-R, straighten} to EMPTY; the oracle is a closed
term.

  * ★ **`LocatedCupThenCap` / `locateCupThenCap_of_not_valley`** — the Type-valued locate.  The shipped locate
    (`hasAdjacentCupThenCap_of_not_valley` / `hasAdjacentCupThenCap_split`) is Prop-valued; the dispatch produces
    a `CellDescentResult` (a `Type`, carrying the `next` cell), so the located split must be DATA, not a Prop
    `∃`.  A structural list recursion (on the spine, guided by the `Bool` valley/cup checks) produces the split
    components plus the cup/cap tags as a structure.
  * ★ **`valleyCellDescentStepOracle`** — the total CLOSED dispatch: locate, classify, `absurd` the excluded case,
    route COMMUTE by `Nat.le_total` on the two left-context widths (right/left producer), STRAIGHTEN by
    `straightenCellDescentStep`.  A closed `CellDescentStepOracle` — no `CellStraightenStepInput` parameter.
  * ★ **`matchingReductsShareSpineTrace_of_valleyTraceEquiv`** — the sharpened reduction:
    `MatchingReductsShareSpineTrace` now follows from `CellValleyTraceEquiv` ALONE (the oracle argument of
    `matchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv` is supplied by the closed dispatch).  The oracle
    is no longer an open input — only Piece II's cell-level trace-equiv remains.

## What this does NOT close (gates stay `false`)

Both the COMMUTE and STRAIGHTEN halves of the oracle are fully DISCHARGED — `valleyCellDescentStepOracle` is a
closed `CellDescentStepOracle`.  What remains owed is `CellValleyTraceEquiv` (the cell-level Piece II block
extractor).  So `MatchingReductsShareSpineTrace`, `convOfMapEq`, and the fib-3 gate flags stay `false` until Piece
II lands.  This file retires `CellStraightenStepInput` and reduces `MatchingReductsShareSpineTrace` to
`CellValleyTraceEquiv` ALONE.

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

/-! ## The total dispatch -/

/-- ★ **The total per-step oracle dispatch — CLOSED (no residual input).**  For any non-valley cell: locate the
innermost cup·cap redex (`locateCupThenCapSpine`), classify it, and route:
`orientationExcludedBothLegs` is refuted (`classifyAdjacentAtoms_ne_orientationExcluded`), `zigZagSharedLeg` is
STRAIGHTENED by `straightenCellDescentStep` (both handednesses dispatched by the width dichotomy — no input, no
`matchingOf` read), `disjointWindows` is COMMUTE — the right/left producer selected by `Nat.le_total` on the two
left-context widths.  Both the COMMUTE and STRAIGHTEN halves are now DISCHARGED; `valleyCellDescentStepOracle` is a
closed `CellDescentStepOracle`, no longer parameterized by any `CellStraightenStepInput`. -/
def valleyCellDescentStepOracle : CellDescentStepOracle :=
  fun cell notValley =>
    let located := locateCupThenCapSpine (spine := cell.spine) notValley
    match hVerdict : classifyAdjacentAtoms located.cupAtom located.capAtom with
    | .orientationExcludedBothLegs =>
        absurd hVerdict
          (classifyAdjacentAtoms_ne_orientationExcluded located.cupAtom located.capAtom
            located.isCupCup located.isCapCap)
    | .zigZagSharedLeg =>
        straightenCellDescentStep cell located.prefixCells located.rest located.isCupCup
          located.isCapCap located.splitEq hVerdict
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

/-- ★ **The sharpened reduction of `MatchingReductsShareSpineTrace`.**  Because the dispatch is now a CLOSED oracle
(the STRAIGHTEN move `straightenCellDescentStep` needs no input), `MatchingReductsShareSpineTrace` follows from the
cell-level Piece II trace-equivalence ALONE.  Composes the closed `valleyCellDescentStepOracle` into
`matchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv`. -/
theorem matchingReductsShareSpineTrace_of_valleyTraceEquiv
    (valleyTraceEquiv : CellValleyTraceEquiv) :
    MatchingReductsShareSpineTrace :=
  matchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv
    valleyCellDescentStepOracle valleyTraceEquiv

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the per-step oracle is CLOSED; both COMMUTE and STRAIGHTEN halves are DISCHARGED.**
`locateCupThenCap_of_not_valley` produces the located cup·cap redex as `Type`-valued DATA (the Prop locate cannot
feed the `Type`-valued `CellDescentResult`); `valleyCellDescentStepOracle` classifies it and routes — the excluded
case refuted, both COMMUTE directions discharged via the two producers selected by `Nat.le_total`, and STRAIGHTEN
discharged by `straightenCellDescentStep` (both handednesses by the width dichotomy, no input, no `matchingOf`
read).  So `valleyCellDescentStepOracle` is a CLOSED `CellDescentStepOracle`, and `MatchingReductsShareSpineTrace`
reduces to `CellValleyTraceEquiv` ALONE (`matchingReductsShareSpineTrace_of_valleyTraceEquiv`).
`CellStraightenStepInput` is RETIRED.

  What this marker does NOT close: `CellValleyTraceEquiv` (the cell-level Piece II block extractor) is still owed.
  So `convOfMapEq`, the keystone `SaturatedMatchingCanonicalization`, and the fib-3 gate flags stay `false`.
  `= true`. -/
def fxMode_hasSpineValleyOracleDispatch : Bool := true

end FX1Poly.Polygraph
