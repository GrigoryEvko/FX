import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyDisorder
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyDescent
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedSpineTraceLift

/-! # mode-3 keystone — Piece I cell driver: the `SaturatedTwoCellConv`-valued fuel-structural descent

`SpineValleyDisorder` closed the descent AT THE PURE-TAG LEVEL: the strictly-decreasing inversion measure
`spineDisorder`, the fuel-structural `valleyDescentDriver`, and its termination/valley-correctness.  The
CELL-level descent cannot ride that tag `List` permutation — the STRAIGHTEN move DELETES two atoms, so the
carrier shrinks — it must be a MIXED recursion: same scalar fuel (`spineDisorder`), a shrinking cell carrier,
and a `SaturatedTwoCellConv` accumulated alongside.

This file ships that mixed recursion's TERMINATION + ACCUMULATION half, cleanly, by structural clone of the tag
driver — upgraded to carry the accumulated `SaturatedTwoCellConv` — PARAMETERIZED by the one genuinely-open input,
a per-step move `oracle`.  The oracle is the honest boundary: it packages, for a non-valley cell, the next cell
with a saturated conversion and a strict disorder drop (the classified STRAIGHTEN | COMMUTE per-step move).  What
this file proves — and it is exactly the explore's "low-risk B4" — is that GIVEN such an oracle the descent
terminates at a valley carrying a `SaturatedTwoCellConv cell (valleyNF cell)`:

  * ★ **`CellDescentResult` / `CellValleyResult`** — the per-step and whole-descent carriers (a next/valley cell,
    the accumulated `SaturatedTwoCellConv`, the disorder drop / valley witness).
  * ★ **`valleyDescentDriverCell`** — the fuel-structural driver (NO `WellFounded.fix`): at a valley return
    `refl`; else fire the oracle, recurse on decremented fuel, glue the conversions by `SaturatedTwoCellConv.trans`.
    The fuel discharge copies the tag driver's `Nat.le_of_lt_succ` argument verbatim.
  * ★ **`valleyNFCell` / `cellDescentConv` / `valleyNFCell_isValley`** — the normal form and its two read-offs:
    a `SaturatedTwoCellConv cell (valleyNFCell cell)` and the valley witness.
  * ★ **`matchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv`** — the honest REDUCTION: given the oracle
    AND the cell-level Piece II input (two VALLEY cells with equal `matchingOf` have trace-equivalent spines), the
    existence residual `MatchingReductsShareSpineTrace` holds.  The reducts are the two valley normal forms; their
    matchings agree by the master hinge `matchingOf_invariant_ofSaturatedConv` (no per-step matching tracking), and
    Piece II supplies the trace equivalence.  No `reify`, no canonical-cell function.

## What this does NOT close — the exact residuals (gates stay `false`)

The driver is oracle-parameterized; the `oracle` itself — a total `CellDescentStepOracle` — is UN-shipped and is
the genuine hard node: the classifier's `zigZagSharedLeg → STRAIGHTEN` branch needs a collapse witness
`cupFrame ⊟ capFrame ≈ id` that window-distance-1 does NOT provide (a shared-leg NON-partner crossing neither
collapses — straighten unavailable — nor commutes — not disjoint), coupling to Piece II's non-crossing partner
discipline and the deferred composite-1-cell whisker functoriality.  And the `valleyTraceEquiv` input is the
cell-level Piece II (the block extractor feeding `valleysWithEqualMatching_spineTraceEquiv`, itself gated on
`cupRestrict_reconstructs`).  So `MatchingReductsShareSpineTrace`, `convOfMapEq`, and the fib-3 gate flags stay
`false`.  This file makes the descent's ACCUMULATION rigorous and isolates the residual to those two inputs.

Raw Lean 4 + Init; the driver is structural recursion on the fuel `Nat` (the tag driver's termination argument,
conv-carrying), the reduction is `matchingOf_invariant_ofSaturatedConv` + saturated `trans`/`symm`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The per-step and whole-descent carriers -/

/-- One descent STEP on a non-valley cell: a next cell, a saturated conversion to it, and a strict disorder drop.
The classified STRAIGHTEN (delete a collapsing snake, disorder drops by deletion) | COMMUTE (transpose disjoint
atoms, disorder drops by the swap) per-step move packaged as data. -/
structure CellDescentResult {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) where
  /-- The cell after one straighten/commute step. -/
  next : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath
  /-- The step is a saturated conversion. -/
  stepConv : SaturatedTwoCellConv cell next
  /-- The step strictly drops the disorder measure. -/
  disorderDrops : spineDisorder next.spine < spineDisorder cell.spine

/-- The whole descent to a valley: a valley cell, the accumulated saturated conversion, and the valley witness. -/
structure CellValleyResult {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) where
  /-- The valley normal form reached. -/
  valley : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath
  /-- The accumulated saturated conversion from the source cell to the valley. -/
  descentConv : SaturatedTwoCellConv cell valley
  /-- The reached cell is a cap-block-then-cup-block valley. -/
  valleyIsValley : isCapThenCupValley SpineAtom.isCupAtom valley.spine = true

/-- The per-step move ORACLE — the one genuinely-open input.  For any non-valley cell it produces a
`CellDescentResult`.  Un-shipped: dispatching STRAIGHTEN (needs a collapse witness the classifier's shared-leg
kind does not supply for a non-partner crossing) vs COMMUTE (needs a disjoint-window spine swap on the typed
cell) is the hard node coupled to Piece II's partner discipline. -/
def CellDescentStepOracle : Type :=
  ∀ {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath),
    isCapThenCupValley SpineAtom.isCupAtom cell.spine = false → CellDescentResult cell

/-! ## The fuel-structural driver -/

/-- ★ **The `SaturatedTwoCellConv`-valued fuel-structural driver.**  While the cell's spine is not a valley, fire
the oracle, recurse on decremented fuel, and glue the accumulated conversion by `SaturatedTwoCellConv.trans`.  NO
`WellFounded.fix` — structural recursion on the fuel `Nat`, whose budget (the initial disorder) is discharged as
sufficient exactly as in the tag driver (`Nat.le_of_lt_succ` on the strict drop).  The base case is `refl` on the
already-a-valley cell — NOT `reify` (the existence route builds no canonical cell). -/
def valleyDescentDriverCell (oracle : CellDescentStepOracle) :
    (fuel : Nat) → {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
    spineDisorder cell.spine ≤ fuel → CellValleyResult cell
  | 0, _, _, _, _, cell, disorderLe =>
      ⟨cell, SaturatedTwoCellConv.refl cell,
        valley_of_disorder_zero SpineAtom.isCupAtom
          (Nat.le_antisymm disorderLe (Nat.zero_le _))⟩
  | fuel + 1, _, _, _, _, cell, disorderLe =>
      match hValley : isCapThenCupValley SpineAtom.isCupAtom cell.spine with
      | true => ⟨cell, SaturatedTwoCellConv.refl cell, hValley⟩
      | false =>
          let step := oracle cell hValley
          let subDescent := valleyDescentDriverCell oracle fuel step.next
            (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le step.disorderDrops disorderLe))
          ⟨subDescent.valley,
            SaturatedTwoCellConv.trans step.stepConv subDescent.descentConv,
            subDescent.valleyIsValley⟩

/-- The valley normal form of a cell — run the driver with fuel equal to the cell's initial disorder. -/
def valleyNFCell (oracle : CellDescentStepOracle) {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath :=
  (valleyDescentDriverCell oracle (spineDisorder cell.spine) cell (Nat.le_refl _)).valley

/-- ★ **The descent conversion** — `cell ≈ valleyNFCell cell`, the accumulated saturated conversion. -/
theorem cellDescentConv (oracle : CellDescentStepOracle) {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    SaturatedTwoCellConv cell (valleyNFCell oracle cell) :=
  (valleyDescentDriverCell oracle (spineDisorder cell.spine) cell (Nat.le_refl _)).descentConv

/-- ★ **The normal form is a valley** — its spine is a cap-block-then-cup-block valley. -/
theorem valleyNFCell_isValley (oracle : CellDescentStepOracle) {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    isCapThenCupValley SpineAtom.isCupAtom (valleyNFCell oracle cell).spine = true :=
  (valleyDescentDriverCell oracle (spineDisorder cell.spine) cell (Nat.le_refl _)).valleyIsValley

/-! ## The reduction of `MatchingReductsShareSpineTrace` to Piece II -/

/-- The cell-level Piece II input — two VALLEY cells with equal boundary matching have trace-equivalent spines.
This is exactly the block extractor feeding `valleysWithEqualMatching_spineTraceEquiv` (Piece II), itself gated on
`cupRestrict_reconstructs`.  Stated as a hypothesis so the reduction is honest about its second residual. -/
def CellValleyTraceEquiv : Prop :=
  ∀ {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (valleyA valleyB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath),
    isCapThenCupValley SpineAtom.isCupAtom valleyA.spine = true →
    isCapThenCupValley SpineAtom.isCupAtom valleyB.spine = true →
    matchingOf valleyA = matchingOf valleyB →
    SpineTraceEquiv adjunctionModeSignature valleyA.spine valleyB.spine

/-- ★ **The honest reduction.**  Given the per-step `oracle` (Piece I descent) AND the cell-level Piece II input
`valleyTraceEquiv`, the existence residual `MatchingReductsShareSpineTrace` holds: instantiate the reducts as the
two valley normal forms.  Each reduct is saturated-convertible to its source (`cellDescentConv`); the reducts'
matchings agree because `matchingOf` is a descent invariant (`matchingOf_invariant_ofSaturatedConv` sandwiching the
hypothesis — NO per-step matching tracking); both reducts are valleys (`valleyNFCell_isValley`); Piece II then
delivers the residual `SpineTraceEquiv`.  No `reify`, no canonical-cell function. -/
theorem matchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv
    (oracle : CellDescentStepOracle) (valleyTraceEquiv : CellValleyTraceEquiv) :
    MatchingReductsShareSpineTrace := by
  intro sourceMode targetMode sourcePath targetPath cellA cellB matchingsEqual
  refine ⟨valleyNFCell oracle cellA, valleyNFCell oracle cellB,
    cellDescentConv oracle cellA, cellDescentConv oracle cellB, ?_⟩
  have matchingReductA : matchingOf (valleyNFCell oracle cellA) = matchingOf cellA :=
    (matchingOf_invariant_ofSaturatedConv (cellDescentConv oracle cellA)).symm
  have matchingReductB : matchingOf (valleyNFCell oracle cellB) = matchingOf cellB :=
    (matchingOf_invariant_ofSaturatedConv (cellDescentConv oracle cellB)).symm
  exact valleyTraceEquiv (valleyNFCell oracle cellA) (valleyNFCell oracle cellB)
    (valleyNFCell_isValley oracle cellA) (valleyNFCell_isValley oracle cellB)
    (matchingReductA.trans (matchingsEqual.trans matchingReductB.symm))

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the mixed-typed `SaturatedTwoCellConv`-valued descent's ACCUMULATION + TERMINATION is
rigorous, and the reduction of `MatchingReductsShareSpineTrace` to Piece II is ISOLATED to exactly two inputs.**
`valleyDescentDriverCell` (fuel-structural, no `WellFounded.fix`) glues the per-step oracle's conversions by
`SaturatedTwoCellConv.trans` down to a valley, discharging the fuel budget by the tag driver's argument; it yields
`cellDescentConv : cell ≈ valleyNFCell cell` and `valleyNFCell_isValley`.  The reduction
`matchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv` derives the existence residual from the oracle plus
the cell-level Piece II, threading the equal matching through the reducts by the master hinge
`matchingOf_invariant_ofSaturatedConv` alone — no per-step matching tracking, no `reify`, no canonical cell.

  What this marker does NOT claim — the two isolated residuals (gates stay `false`):
  * the total per-step `CellDescentStepOracle` — the classifier's `zigZagSharedLeg → STRAIGHTEN` branch needs a
    collapse witness `cupFrame ⊟ capFrame ≈ id` that window-distance-1 does NOT supply (a shared-leg non-partner
    crossing neither collapses nor commutes), coupled to Piece II's non-crossing partner discipline and the
    deferred composite-1-cell whisker functoriality;
  * the `CellValleyTraceEquiv` input — the cell-level Piece II (block extractor →
    `valleysWithEqualMatching_spineTraceEquiv`, gated on `cupRestrict_reconstructs`).

  So Piece I ASSEMBLY is NOT closed: `MatchingReductsShareSpineTrace` reduces to (per-step oracle) AND (cell-level
  Piece II), not to Piece II alone.  `convOfMapEq` and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyCellDriver : Bool := true

end FX1Poly.Polygraph
