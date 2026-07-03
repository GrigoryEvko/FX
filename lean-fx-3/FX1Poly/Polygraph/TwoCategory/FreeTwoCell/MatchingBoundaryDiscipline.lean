import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCoreSwapInRange
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryGodement
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineArityDiscipline

/-! # mode-3 keystone — the boundary-disciplined trace invariance + re-seated soundness

The discharged in-range core swap (`matchingGodementComponentCoreSwap_ofInRange`) carries two
premises the conditions package does not: cup/cap arities on the three participating cells and
the window range at the consuming state.  This file makes BOTH available at every consumption
site and re-seats the soundness capstone on them:

  * `matchingGodementCommute_ofInRange` — the instance-level extract commutation: the two
    transposed Godement run orders extract equally at every conditioned, in-range, cup/cap
    state (the `MatchingGodementComponentCommute` body with the two extra premises explicit,
    collapsing the two chain reductions into one theorem);
  * ★ `traceInvariant_of_boundaryDiscipline` — the ENRICHED trace induction: threading
    `MatchingSwapStateConditions` + `SpineBoundaryChained` + `SpineHasCupCapAtoms` +
    `openWires.length`-tracking through `SpineTraceEquiv`.  The Godement case runs the redex
    entry dichotomy: either the first generator PINS the boundary (the window bound + the
    tracked state discharge the in-range premise, the arity discipline extracts the three cell
    premises) or all four cells are generator-free and both nests collapse to the shared tail;
  * ★ `matchingOf_sound_ofCupCapCells` — the RE-SEATED capstone: full `TwoCellConvFull`
    soundness of `matchingOf` at non-empty source boundaries for cup/cap-disciplined cells —
    every premise seeded by construction at the canonical initial state.  This BYPASSES the
    unconditional `MatchingGodementComponentCoreSwap` Prop (whose blanket form needs premises
    no reachable consumption site lacks, but which the Prop itself cannot see).

The remaining MODE3-B residual is the empty-boundary degeneracy (`sourcePath = nil`, where
`nfPos` fails); the walking-adjunction saturated re-gate additionally consumes THIS capstone at
its cup/cap cells.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Range-length helper (hand-rolled; core `List.length_range` leaks `propext`) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-! ## The instance-level extract commutation under the in-range/cup-cap premises -/

/-- **The instance-level extract commutation.**  At every conditioned state whose window is in
range, with walking-adjunction arities on the three participating cells, the two transposed
Godement run orders extract to the same `DiagramType` — the
`MatchingGodementComponentCommute` body with the two extra premises explicit: the in-range core
swap supplies the sigma bundle, the suffix peel (`matchingComponentRenameRel_full_of_coreSim`)
carries it over the common `cellBetaUpper`-then-`rest` tail, and the closed read-off
(`extractDiagram_of_matchingComponentRenameRel`) lands the equality. -/
theorem matchingGodementCommute_ofInRange {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state)
    (alphaLowCupCap : CellHasCupCapGenerators cellAlpha)
    (alphaCupCap : CellHasCupCapGenerators cellAlphaUpper)
    (betaCupCap : CellHasCupCapGenerators cellBeta)
    (windowsInRange : leftAcc.length + fLow.length + gLow.length ≤ state.openWires.length) :
    extractDiagram bottomCount (processSpine
        (runMatchingCell (runMatchingCell (runMatchingCell
            (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)
      = extractDiagram bottomCount (processSpine
        (runMatchingCell (runMatchingCell (runMatchingCell
            (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest) := by
  obtain ⟨sigma, sigmaFixesZero, fixesBoundary, fixesAbove, sim⟩ :=
    matchingGodementComponentCoreSwap_ofInRange cellAlpha cellAlphaUpper cellBeta leftAcc
      rightAcc bottomCount state conditions alphaLowCupCap alphaCupCap betaCupCap
      windowsInRange
  exact extractDiagram_of_matchingComponentRenameRel bottomCount sigma _ _
    (matchingComponentRenameRel_full_of_coreSim sigma sigmaFixesZero bottomCount fixesBoundary
      _ _ (composePath leftAcc fHigh) rightAcc cellBetaUpper rest fixesAbove sim)

/-! ## The enriched trace induction -/

/-- ★ **The boundary-disciplined trace invariance.**  Threading the reachable-state conditions,
the boundary chain, the cup/cap arity discipline, and the `openWires.length`-tracking through
the full trace-equivalence induction: the extract is invariant.  The Godement case runs the
redex entry dichotomy — the pinned branch feeds the window bound (through the tracked state)
and the extracted cell arities into the in-range commutation; the collapse branch rewrites
both nests to the shared tail.  The `consCongr` case steps all four invariants across the head
atom (`matchingSwapStateConditions_stepAtom` / chain inversion / arity inversion /
`stepAtom_openWires_tracksBoundary`); symmetry and transitivity transport the list-side
premises along the equivalence via `boundaryChainedIff` / `cupCapAtomsIff`. -/
theorem traceInvariant_of_boundaryDiscipline {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList) :
    ∀ (state : WireState) (boundaryLength : Nat),
      MatchingSwapStateConditions bottomCount state →
      SpineBoundaryChained boundaryLength firstList →
      SpineHasCupCapAtoms firstList →
      state.openWires.length = boundaryLength →
      extractAfterProcessing bottomCount state firstList
        = extractAfterProcessing bottomCount state secondList := by
  induction equiv with
  | ofStep step =>
      intro state boundaryLength conditions chained arity tracks
      cases step with
      | godement cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest =>
          cases spineBoundaryChained_interchangeRedex_entryPinned cellAlpha cellAlphaUpper
              cellBeta cellBetaUpper leftAcc rightAcc rest chained with
          | inr bothCollapse => rw [bothCollapse.1, bothCollapse.2]
          | inl entryPinned =>
              have alphaSplit := cellCupCap_and_restAtoms_of_spineDiff _ _ cellAlpha _ arity
              have alphaUpperSplit := cellCupCap_and_restAtoms_of_spineDiff _ _
                cellAlphaUpper _ alphaSplit.2
              have betaSplit := cellCupCap_and_restAtoms_of_spineDiff _ _ cellBeta _
                alphaUpperSplit.2
              have windowLe := interchangeWindow_le_ofEntryPinned leftAcc _ _ rightAcc
                entryPinned
              simp only [extractAfterProcessing, processSpine_spineDiff]
              exact matchingGodementCommute_ofInRange cellAlpha cellAlphaUpper cellBeta
                cellBetaUpper leftAcc rightAcc rest bottomCount state conditions alphaSplit.1
                alphaUpperSplit.1 betaSplit.1 (by rw [tracks]; exact windowLe)
  | refl _ => intro _ _ _ _ _ _; rfl
  | symm inner innerHypothesis =>
      intro state boundaryLength conditions chained arity tracks
      exact (innerHypothesis state boundaryLength conditions
        ((inner.boundaryChainedIff boundaryLength).mpr chained)
        (inner.cupCapAtomsIff.mpr arity) tracks).symm
  | trans firstEquiv _secondEquiv firstHypothesis secondHypothesis =>
      intro state boundaryLength conditions chained arity tracks
      exact (firstHypothesis state boundaryLength conditions chained arity tracks).trans
        (secondHypothesis state boundaryLength conditions
          ((firstEquiv.boundaryChainedIff boundaryLength).mp chained)
          (firstEquiv.cupCapAtomsIff.mp arity) tracks)
  | consCongr atom _ innerHypothesis =>
      intro state boundaryLength conditions chained arity tracks
      have headAndTail := spineBoundaryChained_tail chained
      have arityParts := spineHasCupCapAtoms_tail arity
      exact innerHypothesis (stepAtom state atom) atom.codBoundaryLength
        (matchingSwapStateConditions_stepAtom bottomCount state atom conditions)
        headAndTail.2 arityParts.2
        (stepAtom_openWires_tracksBoundary state atom arityParts.1
          (tracks.trans headAndTail.1.symm))

/-! ## The re-seated soundness capstone -/

/-- ★ **Full `TwoCellConvFull` soundness of `matchingOf` for cup/cap-disciplined cells** at
non-empty source boundaries — the re-seated capstone consuming the DISCHARGED in-range core
swap through the boundary-disciplined trace induction.  Every threaded premise is seeded by
construction at the canonical initial state: the conditions by
`matchingSwapStateConditions_initial`, the boundary chain by `spineBoundaryChained_spine`, the
arity discipline by `spineHasCupCapAtoms_spine`, and the tracking because the initial open
wires ARE `List.range sourcePath.length`.  Unlike `matchingOf_sound_of_componentCoreSwap`,
nothing here is hypothetical — the sigma witness is consumed, not assumed. -/
theorem matchingOf_sound_ofCupCapCells {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (sourceNonEmpty : 0 < sourcePath.length)
    (firstCupCap : CellHasCupCapGenerators firstCell)
    (convFull : TwoCellConvFull signature firstCell secondCell) :
    matchingOf firstCell = matchingOf secondCell :=
  traceInvariant_of_boundaryDiscipline sourcePath.length
    (twoCellConvFull_spineTraceEquiv convFull)
    { openWires := List.range sourcePath.length, links := [], nextFresh := sourcePath.length,
      loops := 0 }
    sourcePath.length
    (matchingSwapStateConditions_initial sourcePath.length sourceNonEmpty)
    firstCell.spineBoundaryChained_spine
    (firstCell.spineHasCupCapAtoms_spine firstCupCap)
    (rangeLength sourcePath.length)

/-! ## Honesty marker -/

/-- **Honesty marker — the boundary-disciplined soundness is SHIPPED.**
`matchingOf_sound_ofCupCapCells`: full `TwoCellConvFull` soundness of `matchingOf` at
non-empty source boundaries for cup/cap-disciplined cells, with the in-range core-swap witness
CONSUMED (not assumed) — the enriched trace induction threads conditions + boundary chain +
arity discipline + state tracking, and the Godement entry dichotomy discharges the in-range
premise at every pinned redex while collapsing generator-free nests.  This bypasses the
unconditional `MatchingGodementComponentCoreSwap` Prop.  NOT yet covered: the empty-boundary
degeneracy (`sourcePath = nil`, where `nfPos` fails at the initial state) and the saturated
walking-adjunction re-gate consuming this capstone — the remaining MODE3-B/E work.  `= true`. -/
def fxMode_hasBoundaryDisciplinedSoundness : Bool := true

end FX1Poly.Polygraph
