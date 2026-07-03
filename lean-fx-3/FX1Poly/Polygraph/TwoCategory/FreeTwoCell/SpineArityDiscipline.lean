import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineGodement

/-! # mode-3 — the spine arity discipline + state boundary tracking (the state side)

The boundary-chain kit (`SpineBoundaryChain` / `SpineBoundaryGodement`) is combinatorial — it
lives on atom lists.  Feeding the discharged in-range core swap needs two more pieces, both on
the STATE side of the matching fold:

  * the LIST-LEVEL cup/cap arity discipline `SpineHasCupCapAtoms` (every atom's generator is a
    `0 ⇒ 2` cup or `2 ⇒ 0` cap), with cons manipulation, PRODUCTION and EXTRACTION across a
    cell's spine difference-list (`CellHasCupCapGenerators` on the cell is exactly cup/cap
    arities on its atoms), invariance across the Godement step and full trace equivalence
    (`SpineGodementStep.cupCapAtomsIff` / `SpineTraceEquiv.cupCapAtomsIff`), and the seed
    (`RawTwoCellExpr.spineHasCupCapAtoms_spine`);
  * the STATE TRACKING lemma `stepAtom_openWires_tracksBoundary`: for a cup/cap atom firing at
    its source boundary, the stepped state's `openWires.length` is exactly the atom's target
    boundary — the bridge from `SpineBoundaryChained` to `state.openWires.length` that the
    enriched trace induction threads through its `consCongr` case.

What remains for MODE3-B after this brick: the enriched trace induction itself (thread
conditions + chain + arity + tracking; the Godement case feeds the entry dichotomy's pinned
branch into `matchingGodementComponentCoreSwap_ofInRange` and closes the collapse branch
trivially) and the re-seated soundness capstone.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Nat cancellation helper (hand-rolled; core `Nat.add_right_cancel` leaks `propext`) -/

private theorem natAddRightCancel : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled = rightSum + cancelled → leftSum = rightSum
  | 0, _, _, sumsEq => sumsEq
  | cancelled + 1, _, _, sumsEq => natAddRightCancel cancelled (Nat.succ.inj sumsEq)

/-! ## The list-level cup/cap arity discipline -/

/-- The list-level cup/cap arity discipline: every atom's generator is a `0 ⇒ 2` cup or a
`2 ⇒ 0` cap.  The spine of every walking-adjunction cell satisfies this. -/
def SpineHasCupCapAtoms {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atomList : List (SpineAtom signature sourceMode targetMode)) : Prop :=
  ∀ atom, atom ∈ atomList → AtomHasCupOrCapArity atom

/-- Cons decomposition of the arity discipline. -/
theorem spineHasCupCapAtoms_tail {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {atom : SpineAtom signature sourceMode targetMode}
    {rest : List (SpineAtom signature sourceMode targetMode)}
    (allAtoms : SpineHasCupCapAtoms (atom :: rest)) :
    AtomHasCupOrCapArity atom ∧ SpineHasCupCapAtoms rest :=
  ⟨allAtoms atom (List.Mem.head rest),
    fun innerAtom innerMem => allAtoms innerAtom (List.Mem.tail atom innerMem)⟩

/-- Cons composition of the arity discipline. -/
theorem spineHasCupCapAtoms_cons {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {atom : SpineAtom signature sourceMode targetMode}
    {rest : List (SpineAtom signature sourceMode targetMode)}
    (headArity : AtomHasCupOrCapArity atom) (restAtoms : SpineHasCupCapAtoms rest) :
    SpineHasCupCapAtoms (atom :: rest) := by
  intro probeAtom probeMem
  cases probeMem with
  | head => exact headArity
  | tail _ innerMem => exact restAtoms probeAtom innerMem

/-! ## Production / extraction across the spine difference-list -/

/-- **Production.**  A cup/cap-disciplined cell contributes only cup/cap atoms: its spine
difference-list satisfies the discipline whenever the rest does. -/
theorem spineHasCupCapAtoms_spineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    CellHasCupCapGenerators cell → SpineHasCupCapAtoms rest →
    SpineHasCupCapAtoms (cell.spineDiff leftAccumulator rightAccumulator rest)
  | _, _, _, _, _, _, .gen _, _, cellCupCap, restAtoms => by
      dsimp only [RawTwoCellExpr.spineDiff]
      exact spineHasCupCapAtoms_cons cellCupCap restAtoms
  | _, _, _, _, _, _, .id _, _, _, restAtoms => restAtoms
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, rest,
      cellCupCap, restAtoms =>
      spineHasCupCapAtoms_spineDiff leftAccumulator rightAccumulator cellAlpha _
        cellCupCap.1
        (spineHasCupCapAtoms_spineDiff leftAccumulator rightAccumulator cellBeta rest
          cellCupCap.2 restAtoms)
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerLeft oneCell body, rest,
      cellCupCap, restAtoms =>
      spineHasCupCapAtoms_spineDiff (composePath leftAccumulator oneCell) rightAccumulator
        body rest cellCupCap restAtoms
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerRight oneCell body, rest,
      cellCupCap, restAtoms =>
      spineHasCupCapAtoms_spineDiff leftAccumulator (composePath oneCell rightAccumulator)
        body rest cellCupCap restAtoms

/-- **Extraction.**  Cup/cap arities on a spine difference-list yield the cell-level discipline
AND the rest's discipline — the converse of production. -/
theorem cellCupCap_and_restAtoms_of_spineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    SpineHasCupCapAtoms (cell.spineDiff leftAccumulator rightAccumulator rest) →
    CellHasCupCapGenerators cell ∧ SpineHasCupCapAtoms rest
  | _, _, _, _, _, _, .gen _, _, allAtoms => by
      dsimp only [RawTwoCellExpr.spineDiff] at allAtoms
      exact spineHasCupCapAtoms_tail allAtoms
  | _, _, _, _, _, _, .id _, _, allAtoms => ⟨True.intro, allAtoms⟩
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, rest,
      allAtoms =>
      have alphaSplit := cellCupCap_and_restAtoms_of_spineDiff leftAccumulator
        rightAccumulator cellAlpha (cellBeta.spineDiff leftAccumulator rightAccumulator rest)
        allAtoms
      have betaSplit := cellCupCap_and_restAtoms_of_spineDiff leftAccumulator
        rightAccumulator cellBeta rest alphaSplit.2
      ⟨⟨alphaSplit.1, betaSplit.1⟩, betaSplit.2⟩
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerLeft oneCell body, rest,
      allAtoms =>
      cellCupCap_and_restAtoms_of_spineDiff (composePath leftAccumulator oneCell)
        rightAccumulator body rest allAtoms
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerRight oneCell body, rest,
      allAtoms =>
      cellCupCap_and_restAtoms_of_spineDiff leftAccumulator
        (composePath oneCell rightAccumulator) body rest allAtoms

/-! ## Invariance across the Godement step + trace equivalence -/

/-- The Godement step preserves the arity discipline in both directions: extract the four cell
disciplines + the tail from one nest, rebuild the other (arity ignores whisker contexts). -/
theorem SpineGodementStep.cupCapAtomsIff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : SpineGodementStep signature firstList secondList) :
    SpineHasCupCapAtoms firstList ↔ SpineHasCupCapAtoms secondList := by
  cases step with
  | godement cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest =>
      constructor
      · intro redexAtoms
        have alphaSplit := cellCupCap_and_restAtoms_of_spineDiff _ _ cellAlpha _ redexAtoms
        have alphaUpperSplit := cellCupCap_and_restAtoms_of_spineDiff _ _ cellAlphaUpper _
          alphaSplit.2
        have betaSplit := cellCupCap_and_restAtoms_of_spineDiff _ _ cellBeta _
          alphaUpperSplit.2
        have betaUpperSplit := cellCupCap_and_restAtoms_of_spineDiff _ _ cellBetaUpper _
          betaSplit.2
        exact spineHasCupCapAtoms_spineDiff _ _ cellAlpha _ alphaSplit.1
          (spineHasCupCapAtoms_spineDiff _ _ cellBeta _ betaSplit.1
            (spineHasCupCapAtoms_spineDiff _ _ cellAlphaUpper _ alphaUpperSplit.1
              (spineHasCupCapAtoms_spineDiff _ _ cellBetaUpper _ betaUpperSplit.1
                betaUpperSplit.2)))
      · intro reductAtoms
        have alphaSplit := cellCupCap_and_restAtoms_of_spineDiff _ _ cellAlpha _ reductAtoms
        have betaSplit := cellCupCap_and_restAtoms_of_spineDiff _ _ cellBeta _ alphaSplit.2
        have alphaUpperSplit := cellCupCap_and_restAtoms_of_spineDiff _ _ cellAlphaUpper _
          betaSplit.2
        have betaUpperSplit := cellCupCap_and_restAtoms_of_spineDiff _ _ cellBetaUpper _
          alphaUpperSplit.2
        exact spineHasCupCapAtoms_spineDiff _ _ cellAlpha _ alphaSplit.1
          (spineHasCupCapAtoms_spineDiff _ _ cellAlphaUpper _ alphaUpperSplit.1
            (spineHasCupCapAtoms_spineDiff _ _ cellBeta _ betaSplit.1
              (spineHasCupCapAtoms_spineDiff _ _ cellBetaUpper _ betaUpperSplit.1
                betaUpperSplit.2)))

/-- Full trace equivalence preserves the arity discipline. -/
theorem SpineTraceEquiv.cupCapAtomsIff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList) :
    SpineHasCupCapAtoms firstList ↔ SpineHasCupCapAtoms secondList := by
  induction equiv with
  | ofStep step => exact step.cupCapAtomsIff
  | refl _ => exact Iff.rfl
  | symm _ innerIff => exact innerIff.symm
  | trans _ _ leftIff rightIff => exact leftIff.trans rightIff
  | consCongr atom _ tailIff =>
      constructor
      · intro allFirst
        have headAndTail := spineHasCupCapAtoms_tail allFirst
        exact spineHasCupCapAtoms_cons headAndTail.1 (tailIff.mp headAndTail.2)
      · intro allSecond
        have headAndTail := spineHasCupCapAtoms_tail allSecond
        exact spineHasCupCapAtoms_cons headAndTail.1 (tailIff.mpr headAndTail.2)

/-- The seed: the spine of a cup/cap-disciplined cell satisfies the list-level discipline. -/
theorem RawTwoCellExpr.spineHasCupCapAtoms_spine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath)
    (cellCupCap : CellHasCupCapGenerators cell) :
    SpineHasCupCapAtoms cell.spine := by
  dsimp only [RawTwoCellExpr.spine]
  exact spineHasCupCapAtoms_spineDiff (identityPath sourceMode) (identityPath targetMode)
    cell [] cellCupCap (fun _ absurdMem => by cases absurdMem)

/-! ## State boundary tracking through one atom -/

/-- ★ **The state tracks the boundary chain.**  For a cup/cap atom firing at its source
boundary width, the stepped state's open-wire count is exactly the atom's target boundary
width — the additive count shift of `stepAtom_openWiresSuffix_invariant` read at a tracked
state (the window premise holds with the right context as slack). -/
theorem stepAtom_openWires_tracksBoundary {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength) :
    (stepAtom state atom).openWires.length = atom.codBoundaryLength := by
  have windowInRange : atom.leftContext.length + atom.generatorDom.length
      ≤ state.openWires.length := by
    rw [tracksEntry]
    exact Nat.le_add_right (atom.leftContext.length + atom.generatorDom.length)
      atom.rightContext.length
  have countShift := (stepAtom_openWiresSuffix_invariant state atom 0 arity windowInRange).2
  have paddedTracks : (stepAtom state atom).openWires.length + atom.generatorDom.length
      = atom.codBoundaryLength + atom.generatorDom.length := by
    rw [countShift, tracksEntry]
    show atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length
        + atom.generatorCod.length
      = atom.leftContext.length + atom.generatorCod.length + atom.rightContext.length
        + atom.generatorDom.length
    rw [Nat.add_right_comm (atom.leftContext.length + atom.generatorDom.length)
        atom.rightContext.length atom.generatorCod.length,
      Nat.add_right_comm atom.leftContext.length atom.generatorDom.length
        atom.generatorCod.length,
      Nat.add_right_comm (atom.leftContext.length + atom.generatorCod.length)
        atom.generatorDom.length atom.rightContext.length]
  exact natAddRightCancel atom.generatorDom.length paddedTracks

/-! ## Honesty marker -/

/-- **Honesty marker — the arity discipline + state tracking kit is SHIPPED.**  The list-level
cup/cap discipline (`SpineHasCupCapAtoms`) with cons manipulation, production/extraction
across spine difference-lists, invariance across the Godement step and full trace equivalence,
the cell-level seed, and the per-atom state tracking bridge
(`stepAtom_openWires_tracksBoundary`).  NOT yet covered: the enriched trace induction that
threads conditions + boundary chain + arity discipline + state tracking, feeding the entry
dichotomy's pinned branch into the discharged in-range core swap — the next brick.  `= true`. -/
def fxMode_hasSpineArityDisciplineKit : Bool := true

end FX1Poly.Polygraph
