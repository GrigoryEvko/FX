import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # FreeTwoCell/AtomicSwapBoundary — the swap closure preserves the boundary chain

The peel's iteration invariant at the GENERAL signature: an adjacent atomic swap replaces two
whisker-factored atoms by their transposition, and both orders fire at the same running
boundary — every boundary sum is the same five-part total `|leftAcc| + |window| + |inert| +
|window'| + |rightAcc|` under different associations.  Hence `SpineBoundaryChained` transfers
along a single `SpineAtomSwap` (both directions) and, by closure induction, along the whole
`AtomicTraceEquiv` — so a peel walking a trace-equivalence chain can thread ONE chainedness
hypothesis through every swap, symmetry, and cons step.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Flattening a doubly-composed path's length in one step. -/
theorem composePath_length_double {graph : ModeGraph}
    {startMode innerMode outerMode finishMode : graph.Mode}
    (firstLeg : ModalityPath graph startMode innerMode)
    (secondLeg : ModalityPath graph innerMode outerMode)
    (thirdLeg : ModalityPath graph outerMode finishMode) :
    (composePath (composePath firstLeg secondLeg) thirdLeg).length
      = firstLeg.length + secondLeg.length + thirdLeg.length := by
  rw [composePath_length (composePath firstLeg secondLeg) thirdLeg,
    composePath_length firstLeg secondLeg]

/-- Reassociating the five-part boundary sum: nested tail to flat left-associated. -/
theorem natSumFive_ofNestedTail
    (firstPart secondPart thirdPart fourthPart fifthPart : Nat) :
    firstPart + secondPart + ((thirdPart + fourthPart) + fifthPart)
      = firstPart + secondPart + thirdPart + fourthPart + fifthPart := by
  rw [← Nat.add_assoc (firstPart + secondPart) (thirdPart + fourthPart) fifthPart,
    ← Nat.add_assoc (firstPart + secondPart) thirdPart fourthPart]

/-- ★ **One atomic swap preserves the boundary chain (source to target).**  Every dom/cod
boundary of the four atoms involved is the same five-part sum under a different association. -/
theorem spineBoundaryChained_target_of_spineAtomSwap {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} {boundaryLength : Nat}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (swapStep : SpineAtomSwap signature firstList secondList)
    (chained : SpineBoundaryChained boundaryLength firstList) :
    SpineBoundaryChained boundaryLength secondList := by
  cases swapStep with
  | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode
      oneCellFMid oneCellFHigh oneCellGLow oneCellGMid
      generatorLeft generatorRight leftAcc inertPath rightAcc rest =>
      obtain ⟨firesFirst, tailChained⟩ := spineBoundaryChained_tail chained
      obtain ⟨_, restChained⟩ := spineBoundaryChained_tail tailChained
      have firesFlat : leftAcc.length + oneCellFMid.length
          + (composePath (composePath inertPath oneCellGLow) rightAcc).length
          = boundaryLength := firesFirst
      rw [composePath_length_double inertPath oneCellGLow rightAcc,
        natSumFive_ofNestedTail leftAcc.length oneCellFMid.length inertPath.length
          oneCellGLow.length rightAcc.length] at firesFlat
      have codsEqual : (⟨swapMiddleRight, swapTargetMode,
            composePath (composePath leftAcc oneCellFHigh) inertPath, oneCellGLow,
            oneCellGMid, generatorRight, rightAcc⟩ :
              SpineAtom signature overallSource overallTarget).codBoundaryLength
          = (⟨swapSourceMode, swapMiddleLeft, leftAcc, oneCellFMid, oneCellFHigh,
              generatorLeft, composePath (composePath inertPath oneCellGMid) rightAcc⟩ :
              SpineAtom signature overallSource overallTarget).codBoundaryLength := by
        show (composePath (composePath leftAcc oneCellFHigh) inertPath).length
              + oneCellGMid.length + rightAcc.length
            = leftAcc.length + oneCellFHigh.length
              + (composePath (composePath inertPath oneCellGMid) rightAcc).length
        rw [composePath_length_double leftAcc oneCellFHigh inertPath,
          composePath_length_double inertPath oneCellGMid rightAcc,
          natSumFive_ofNestedTail leftAcc.length oneCellFHigh.length inertPath.length
            oneCellGMid.length rightAcc.length]
      refine SpineBoundaryChained.cons _ ?_ (SpineBoundaryChained.cons _ ?_ ?_)
      · show (composePath (composePath leftAcc oneCellFMid) inertPath).length
            + oneCellGLow.length + rightAcc.length = boundaryLength
        rw [composePath_length_double leftAcc oneCellFMid inertPath]
        exact firesFlat
      · show leftAcc.length + oneCellFMid.length
            + (composePath (composePath inertPath oneCellGMid) rightAcc).length
          = (composePath (composePath leftAcc oneCellFMid) inertPath).length
            + oneCellGMid.length + rightAcc.length
        rw [composePath_length_double inertPath oneCellGMid rightAcc,
          composePath_length_double leftAcc oneCellFMid inertPath,
          natSumFive_ofNestedTail leftAcc.length oneCellFMid.length inertPath.length
            oneCellGMid.length rightAcc.length]
      · exact codsEqual ▸ restChained

/-- ★ **One atomic swap preserves the boundary chain (target back to source).** -/
theorem spineBoundaryChained_source_of_spineAtomSwap {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} {boundaryLength : Nat}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (swapStep : SpineAtomSwap signature firstList secondList)
    (chained : SpineBoundaryChained boundaryLength secondList) :
    SpineBoundaryChained boundaryLength firstList := by
  cases swapStep with
  | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode
      oneCellFMid oneCellFHigh oneCellGLow oneCellGMid
      generatorLeft generatorRight leftAcc inertPath rightAcc rest =>
      obtain ⟨firesFirst, tailChained⟩ := spineBoundaryChained_tail chained
      obtain ⟨_, restChained⟩ := spineBoundaryChained_tail tailChained
      have firesFlat : (composePath (composePath leftAcc oneCellFMid) inertPath).length
          + oneCellGLow.length + rightAcc.length = boundaryLength := firesFirst
      rw [composePath_length_double leftAcc oneCellFMid inertPath] at firesFlat
      have codsEqual : (⟨swapSourceMode, swapMiddleLeft, leftAcc, oneCellFMid, oneCellFHigh,
            generatorLeft, composePath (composePath inertPath oneCellGMid) rightAcc⟩ :
              SpineAtom signature overallSource overallTarget).codBoundaryLength
          = (⟨swapMiddleRight, swapTargetMode,
              composePath (composePath leftAcc oneCellFHigh) inertPath, oneCellGLow,
              oneCellGMid, generatorRight, rightAcc⟩ :
              SpineAtom signature overallSource overallTarget).codBoundaryLength := by
        show leftAcc.length + oneCellFHigh.length
              + (composePath (composePath inertPath oneCellGMid) rightAcc).length
            = (composePath (composePath leftAcc oneCellFHigh) inertPath).length
              + oneCellGMid.length + rightAcc.length
        rw [composePath_length_double inertPath oneCellGMid rightAcc,
          composePath_length_double leftAcc oneCellFHigh inertPath,
          natSumFive_ofNestedTail leftAcc.length oneCellFHigh.length inertPath.length
            oneCellGMid.length rightAcc.length]
      refine SpineBoundaryChained.cons _ ?_ (SpineBoundaryChained.cons _ ?_ ?_)
      · show leftAcc.length + oneCellFMid.length
            + (composePath (composePath inertPath oneCellGLow) rightAcc).length
          = boundaryLength
        rw [composePath_length_double inertPath oneCellGLow rightAcc,
          natSumFive_ofNestedTail leftAcc.length oneCellFMid.length inertPath.length
            oneCellGLow.length rightAcc.length]
        exact firesFlat
      · show (composePath (composePath leftAcc oneCellFHigh) inertPath).length
            + oneCellGLow.length + rightAcc.length
          = leftAcc.length + oneCellFHigh.length
            + (composePath (composePath inertPath oneCellGLow) rightAcc).length
        rw [composePath_length_double leftAcc oneCellFHigh inertPath,
          composePath_length_double inertPath oneCellGLow rightAcc,
          natSumFive_ofNestedTail leftAcc.length oneCellFHigh.length inertPath.length
            oneCellGLow.length rightAcc.length]
      · exact codsEqual ▸ restChained

/-- ★ **The boundary chain transfers along the WHOLE atomic trace equivalence** — the peel's
iteration invariant, packaged once: swaps transfer by the two lemmas above, and the closure
operators (refl / symm / trans / cons) are chain-transparent. -/
theorem spineBoundaryChained_iff_of_atomicTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv signature firstList secondList) :
    ∀ boundaryLength : Nat,
      SpineBoundaryChained boundaryLength firstList
        ↔ SpineBoundaryChained boundaryLength secondList := by
  induction traceEquiv with
  | ofSwap swapStep =>
      exact fun boundaryLength => Iff.intro
        (spineBoundaryChained_target_of_spineAtomSwap swapStep)
        (spineBoundaryChained_source_of_spineAtomSwap swapStep)
  | refl _ => exact fun _ => Iff.rfl
  | symm _ innerIff => exact fun boundaryLength => (innerIff boundaryLength).symm
  | trans _ _ leftIff rightIff =>
      exact fun boundaryLength => (leftIff boundaryLength).trans (rightIff boundaryLength)
  | consCongr atom _ tailIff =>
      intro boundaryLength
      constructor
      · intro chained
        obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
        exact SpineBoundaryChained.cons atom headFires
          ((tailIff atom.codBoundaryLength).mp tailChained)
      · intro chained
        obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
        exact SpineBoundaryChained.cons atom headFires
          ((tailIff atom.codBoundaryLength).mpr tailChained)

end FX1Poly.Polygraph
