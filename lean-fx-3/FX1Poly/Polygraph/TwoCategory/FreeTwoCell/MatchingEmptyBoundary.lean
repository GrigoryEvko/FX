import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingBoundaryDiscipline
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCounterShift

/-! # mode-3 — the empty-boundary soundness capstone (MODE3-B closes)

`matchingOf_sound_ofCupCapCells` covers non-empty source boundaries; the degenerate boundary
(`sourcePath.length = 0`) fails its `nfPos` condition at the canonical seed `⟨[], [], 0, 0⟩`.
This file closes the gap through the counter-shift PROXY:

  * `matchingOf_sound_ofCupCapCells_emptyBoundary` — the three-step chain: the counter-shift
    bridge exchanges the degenerate seed for the proxy seed `⟨[], [], 1, 0⟩` on the first
    cell's spine; the proxy satisfies the FULL conditions package (bottom `0 ≤ 1`, empty
    forest, positive counter, vacuous freshness), so the boundary-disciplined trace invariance
    applies verbatim across the trace equivalence; the bridge exchanges back on the second
    cell's spine.  The boundary chain and arity discipline transport along the equivalence via
    `boundaryChainedIff` / `cupCapAtomsIff`;
  * ★ `matchingOf_sound_ofCupCapCells_allBoundaries` — the TOTAL capstone: full
    `TwoCellConvFull` soundness of `matchingOf` for cup/cap-disciplined cells at EVERY source
    boundary, dispatching on the boundary length.

This closes the MODE3-B arc: the sigma witness is consumed at every boundary, empty included.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The empty-boundary soundness leg.**  At a degenerate source boundary the canonical seed
`⟨[], [], 0, 0⟩` fails `nfPos`, so the run is exchanged (via the counter-shift bridge) for the
same run from the PROXY seed `⟨[], [], 1, 0⟩`, where the full conditions package holds and the
boundary-disciplined trace invariance applies; the bridge on the second cell's spine (its chain
and arity transported along the trace equivalence) exchanges back. -/
theorem matchingOf_sound_ofCupCapCells_emptyBoundary {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (sourceEmpty : sourcePath.length = 0)
    (firstCupCap : CellHasCupCapGenerators firstCell)
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    matchingOf firstCell = matchingOf secondCell := by
  have equiv := twoCellConvFull_spineTraceEquiv convFull
  have chainedFirst : SpineBoundaryChained 0 firstCell.spine :=
    sourceEmpty ▸ firstCell.spineBoundaryChained_spine
  have arityFirst : SpineHasCupCapAtoms firstCell.spine :=
    firstCell.spineHasCupCapAtoms_spine firstCupCap
  have chainedSecond : SpineBoundaryChained 0 secondCell.spine :=
    (equiv.boundaryChainedIff 0).mp chainedFirst
  have aritySecond : SpineHasCupCapAtoms secondCell.spine :=
    equiv.cupCapAtomsIff.mp arityFirst
  have proxyConditions : MatchingSwapStateConditions 0
      { openWires := [], links := [], nextFresh := 1, loops := 0 } :=
    { bottomLe := Nat.zero_le 1
      forest := by exact True.intro
      nfPos := Nat.lt_succ_self 0
      fresh := ⟨fun _ absurdMem => (by cases absurdMem),
        fun _ absurdMem => (by cases absurdMem)⟩ }
  have firstShift := extractAfterProcessing_emptyBoundary_counterShift firstCell.spine
    chainedFirst arityFirst
  have secondShift := extractAfterProcessing_emptyBoundary_counterShift secondCell.spine
    chainedSecond aritySecond
  have proxyInvariant := traceInvariant_of_boundaryDiscipline 0 equiv
    { openWires := [], links := [], nextFresh := 1, loops := 0 } 0
    proxyConditions chainedFirst arityFirst rfl
  show matchingOfSpineList sourcePath.length firstCell.spine
    = matchingOfSpineList sourcePath.length secondCell.spine
  rw [sourceEmpty]
  exact (firstShift.trans proxyInvariant).trans secondShift.symm

/-- ★ **Full `TwoCellConvFull` soundness of `matchingOf` for cup/cap-disciplined cells at EVERY
source boundary** — the MODE3-B total capstone, dispatching on the boundary length: the
positive case is the boundary-disciplined capstone (conditions seeded at the canonical initial
state), the empty case the counter-shift proxy chain. -/
theorem matchingOf_sound_ofCupCapCells_allBoundaries {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (firstCupCap : CellHasCupCapGenerators firstCell)
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    matchingOf firstCell = matchingOf secondCell := by
  cases boundaryCases : sourcePath.length with
  | zero =>
      exact matchingOf_sound_ofCupCapCells_emptyBoundary boundaryCases firstCupCap convFull
  | succ boundaryPredecessor =>
      exact matchingOf_sound_ofCupCapCells
        (by
          rw [boundaryCases]
          exact Nat.succ_le_succ (Nat.zero_le boundaryPredecessor))
        firstCupCap convFull

/-! ## Honesty marker -/

/-- **Honesty marker — `matchingOf` soundness at ALL boundaries is SHIPPED.**
`matchingOf_sound_ofCupCapCells_allBoundaries`: full `TwoCellConvFull` soundness of
`matchingOf` for cup/cap-disciplined cells at every source boundary — positive boundaries via
the boundary-disciplined trace invariance seeded at the canonical initial state, the empty
boundary via the counter-shift proxy (the degenerate seed exchanged for `⟨[], [], 1, 0⟩` where
the conditions package holds).  The sigma witness is CONSUMED at every boundary; the MODE3-B
arc closes.  Remaining mode-3 work: the saturated walking-adjunction re-gate consuming this
capstone (MODE3-C), the Joyal–Street reconstruction (MODE3-D), and the gate flips (MODE3-E).
`= true`. -/
def fxMode_hasMatchingSoundnessAllBoundaries : Bool := true

end FX1Poly.Polygraph
