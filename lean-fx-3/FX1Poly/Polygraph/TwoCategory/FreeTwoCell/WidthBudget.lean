import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryGodement
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapGeneration

/-! # WidthBudget — chained atom widths are budget-bounded, and the budget rides (FREE-7)

Third finiteness leg of the BOUNDED-ATOM-UNIVERSE route: on a boundary-chained trace,
every atom fires at a width reachable from the initial boundary by the earlier atoms'
growth, so every width — and hence every whisker-context length — is bounded by the
initial width plus a TOTAL GROWTH BUDGET.  The budget is deliberately crude (the sum of
the generators' target-boundary lengths — no truncated subtraction anywhere) because
the universe only needs finiteness, not tightness; and it reads only the generators,
which ride through swaps, so it is a class invariant.

  * `traceGrowthBudget` — the crude budget: the sum of the atoms' `generatorCod`
    lengths (cons-only);
  * `SpineAtom.codBoundaryLength_le` — one atom widens the boundary by at most its
    own target length;
  * ★ `spineBoundaryChained_boundsAtomWidth` — chain induction: every atom of a
    chained trace fires within `initialWidth + budget`;
  * `AtomicTraceEquiv.growthBudgetEq` — the budget is a class invariant (swaps
    transpose the two head generators; `Nat.add_left_comm` closes);
  * ★ `memberAtomWidth_bounded_ofSeed` — the universe-facing corollary: every atom of
    every class member of a CHAINED seed fires within `initialWidth + seedBudget`
    (chainedness transfers by the shipped `SpineTraceEquiv.boundaryChainedIff` through
    the FREE-5 identification);
  * `SpineAtom.leftContextLength_le_domBoundaryLength` /
    `rightContextLength_le_domBoundaryLength` — the context lengths the universe
    enumerates are below the atom's firing width.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The crude growth budget -/

/-- The trace's total width-growth budget: the sum of the generators' target-boundary
lengths (cons-only).  Crude on purpose — no subtraction, and it reads only the
generators, which swaps never change. -/
def traceGrowthBudget {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    List (SpineAtom signature sourceMode targetMode) → Nat
  | [] => 0
  | atom :: rest => atom.generatorCod.length + traceGrowthBudget rest

/-! ## Per-atom width facts -/

/-- Firing one atom widens the boundary by at most the generator's target length. -/
theorem SpineAtom.codBoundaryLength_le {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) :
    atom.codBoundaryLength ≤ atom.domBoundaryLength + atom.generatorCod.length := by
  show atom.leftContext.length + atom.generatorCod.length + atom.rightContext.length
    ≤ atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length
        + atom.generatorCod.length
  rw [Nat.add_right_comm (atom.leftContext.length + atom.generatorDom.length)
    atom.rightContext.length atom.generatorCod.length]
  exact Nat.add_le_add_right
    (Nat.add_le_add_right
      (Nat.le_add_right atom.leftContext.length atom.generatorDom.length)
      atom.generatorCod.length)
    atom.rightContext.length

/-- The left whisker context is no longer than the atom's firing width. -/
theorem SpineAtom.leftContextLength_le_domBoundaryLength {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) :
    atom.leftContext.length ≤ atom.domBoundaryLength :=
  Nat.le_trans
    (Nat.le_add_right atom.leftContext.length atom.generatorDom.length)
    (Nat.le_add_right (atom.leftContext.length + atom.generatorDom.length)
      atom.rightContext.length)

/-- The right whisker context is no longer than the atom's firing width. -/
theorem SpineAtom.rightContextLength_le_domBoundaryLength {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) :
    atom.rightContext.length ≤ atom.domBoundaryLength :=
  Nat.le_add_left atom.rightContext.length
    (atom.leftContext.length + atom.generatorDom.length)

/-! ## ★ The chained width bound -/

/-- ★ **Chained atom widths are budget-bounded**: every atom of a boundary-chained trace
fires within the initial width plus the trace's growth budget — the head fires exactly
at the initial width, and the tail's initial width is at most one head-growth above
it. -/
theorem spineBoundaryChained_boundsAtomWidth {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} {boundaryLength : Nat}
    {trace : List (SpineAtom signature sourceMode targetMode)}
    (chained : SpineBoundaryChained boundaryLength trace) :
    ∀ {atom : SpineAtom signature sourceMode targetMode}, atom ∈ trace →
      atom.domBoundaryLength ≤ boundaryLength + traceGrowthBudget trace := by
  induction chained with
  | nil _ =>
      intro atom atomMem
      exact (nomatch atomMem)
  | @cons caseBoundary headAtom _caseRest headFiresAtBoundary _tailChained
      innerHypothesis =>
      intro atom atomMem
      cases atomMem with
      | head =>
          rw [headFiresAtBoundary]
          exact Nat.le_add_right _ _
      | tail _ tailMem =>
          have tailWidthBound := innerHypothesis tailMem
          have handedWidthBounded : headAtom.codBoundaryLength
              ≤ caseBoundary + headAtom.generatorCod.length := by
            rw [← headFiresAtBoundary]
            exact headAtom.codBoundaryLength_le
          have liftedBound := Nat.le_trans tailWidthBound
            (Nat.add_le_add_right handedWidthBounded _)
          rw [Nat.add_assoc] at liftedBound
          exact liftedBound

/-! ## The budget is a class invariant -/

/-- The growth budget reads only the generators, which ride through swaps — one swap
transposes the two head summands. -/
theorem AtomicTraceEquiv.growthBudgetEq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv signature firstList secondList) :
    traceGrowthBudget firstList = traceGrowthBudget secondList := by
  induction traceEquiv with
  | ofSwap swapStep =>
      cases swapStep with
      | @swap _swapSourceMode _swapMiddleLeft _swapMiddleRight _swapTargetMode _oneCellFMid
          oneCellFHigh _oneCellGLow oneCellGMid _generatorLeft _generatorRight _leftAcc
          _inertPath _rightAcc rest =>
          exact Nat.add_left_comm oneCellFHigh.length oneCellGMid.length
            (traceGrowthBudget rest)
  | refl _ => rfl
  | symm _ innerHypothesis => exact innerHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis
  | consCongr atom _ innerHypothesis =>
      exact congrArg (Nat.add atom.generatorCod.length) innerHypothesis

/-! ## ★ The universe-facing corollary -/

/-- ★ **Member atom widths are seed-bounded**: every atom of every class member of a
boundary-chained seed fires within the seed's initial width plus the seed's growth
budget — chainedness transfers across the class, the budget rides. -/
theorem memberAtomWidth_bounded_ofSeed {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {seedTrace memberTrace : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv signature seedTrace memberTrace)
    {boundaryLength : Nat}
    (seedChained : SpineBoundaryChained boundaryLength seedTrace)
    {atom : SpineAtom signature overallSource overallTarget}
    (atomMem : atom ∈ memberTrace) :
    atom.domBoundaryLength ≤ boundaryLength + traceGrowthBudget seedTrace := by
  have memberChained : SpineBoundaryChained boundaryLength memberTrace :=
    ((spineTraceEquiv_iff_atomicTraceEquiv.mpr traceEquiv).boundaryChainedIff
      boundaryLength).mp seedChained
  rw [traceEquiv.growthBudgetEq]
  exact spineBoundaryChained_boundsAtomWidth memberChained atomMem

end FX1Poly.Polygraph
