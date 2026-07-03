import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Spine

/-! # mode-3 — the spine boundary-chain discipline (the in-range substrate)

The matching soundness chain consumes the component core swap at arbitrary trace-induction
states, where the in-range read premise (`window ≤ openWires.length`) of the discharged
`matchingGodementComponentCoreSwap_ofInRange` is not directly available.  What makes it
available is a BOUNDARY invariant: states arising from processing a well-formed spine keep
`openWires.length` equal to the current 1-cell boundary width, and the spine atoms of an actual
2-cell CHAIN those widths — each atom fires exactly at the running boundary (left whisker
context + generator source + right whisker context) and hands its target boundary to the tail.

This file ships that combinatorial substrate:

  * `SpineAtom.domBoundaryLength` / `SpineAtom.codBoundaryLength` — the atom's full
    source/target boundary widths;
  * `SpineBoundaryChained` — the chain discipline on atom lists, with cons inversion
    (`spineBoundaryChained_tail`);
  * `RawTwoCellExpr.sourcePath_eq_targetPath_of_generatorCount_zero` /
    `RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero` — generator-free cells are
    boundary-silent: parallel boundaries coincide and the spine contribution is empty;
  * `spineBoundaryChained_spineDiff` (production) — a cell's spine difference-list is chained
    from its source boundary whenever the rest is chained from its target boundary;
  * `spineBoundaryChained_rest_of_spineDiff` (inversion) — peeling a cell's spine contribution
    off a chain at the source boundary leaves the rest chained at the target boundary;
  * `spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero` — a generator-carrying cell
    PINS the chain boundary to its source-boundary width (the lemma that will extract the
    in-range premise at a Godement redex);
  * `RawTwoCellExpr.spineBoundaryChained_spine` — the initial-state seed: every cell's spine is
    chained from its source 1-cell's length.

The next brick consumes these at the Godement redex/reduct nests (the four-cell window bound +
chain preservation), then threads the invariant through the conditioned trace induction.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Nat successor disequality (hand-rolled; core `Nat.succ_ne_zero` leaks `propext`) -/

private theorem natSuccNeZero (anyNat : Nat) : Nat.succ anyNat ≠ 0 := fun succEqZero =>
  Nat.noConfusion succEqZero

/-! ## Boundary widths + the chain discipline -/

/-- The full SOURCE boundary width at which an atom fires: left whisker context, then the
generator's source 1-cell, then the right whisker context. -/
def SpineAtom.domBoundaryLength {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) : Nat :=
  atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length

/-- The full TARGET boundary width an atom leaves behind: left whisker context, then the
generator's target 1-cell, then the right whisker context. -/
def SpineAtom.codBoundaryLength {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) : Nat :=
  atom.leftContext.length + atom.generatorCod.length + atom.rightContext.length

/-- The boundary-chain discipline on spine-atom lists: every atom fires exactly at the running
boundary width and hands its target boundary width to the tail.  The empty list is chained at
any boundary (it constrains nothing). -/
inductive SpineBoundaryChained {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    Nat → List (SpineAtom signature sourceMode targetMode) → Prop where
  /-- The empty spine is chained at any boundary. -/
  | nil (boundaryLength : Nat) : SpineBoundaryChained boundaryLength []
  /-- A cons is chained when the head fires at the running boundary and the tail is chained at
  the head's target boundary. -/
  | cons {boundaryLength : Nat} (atom : SpineAtom signature sourceMode targetMode)
      {rest : List (SpineAtom signature sourceMode targetMode)}
      (headFiresAtBoundary : atom.domBoundaryLength = boundaryLength)
      (tailChained : SpineBoundaryChained atom.codBoundaryLength rest) :
      SpineBoundaryChained boundaryLength (atom :: rest)

/-- Cons inversion for the chain discipline: the head fires at the running boundary and the tail
is chained at the head's target boundary. -/
theorem spineBoundaryChained_tail {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} {boundaryLength : Nat}
    {atom : SpineAtom signature sourceMode targetMode}
    {rest : List (SpineAtom signature sourceMode targetMode)}
    (chained : SpineBoundaryChained boundaryLength (atom :: rest)) :
    atom.domBoundaryLength = boundaryLength
      ∧ SpineBoundaryChained atom.codBoundaryLength rest := by
  cases chained with
  | cons _ headFiresAtBoundary tailChained => exact ⟨headFiresAtBoundary, tailChained⟩

/-! ## Generator-free cells are boundary-silent -/

/-- A generator-free 2-cell expression relates a 1-cell boundary to ITSELF: with no generating
2-cell anywhere, every constructor preserves the boundary on the nose. -/
theorem RawTwoCellExpr.sourcePath_eq_targetPath_of_generatorCount_zero
    {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    (cell : RawTwoCellExpr signature sourcePath targetPath) →
    cell.generatorCount = 0 → sourcePath = targetPath
  | _, _, _, _, .gen _, countEq => absurd countEq (natSuccNeZero 0)
  | _, _, _, _, .id _, _ => rfl
  | _, _, _, _, .vcomp cellAlpha cellBeta, countZero => by
      dsimp only [RawTwoCellExpr.generatorCount] at countZero
      have alphaZero : cellAlpha.generatorCount = 0 := by
        cases alphaProbe : cellAlpha.generatorCount with
        | zero => rfl
        | succ predecessorCount =>
            rw [alphaProbe, Nat.succ_add] at countZero
            exact absurd countZero (natSuccNeZero _)
      have betaZero : cellBeta.generatorCount = 0 := by
        cases betaProbe : cellBeta.generatorCount with
        | zero => rfl
        | succ predecessorCount =>
            rw [betaProbe, Nat.add_succ] at countZero
            exact absurd countZero (natSuccNeZero _)
      exact (RawTwoCellExpr.sourcePath_eq_targetPath_of_generatorCount_zero cellAlpha
        alphaZero).trans
        (RawTwoCellExpr.sourcePath_eq_targetPath_of_generatorCount_zero cellBeta betaZero)
  | _, _, _, _, @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell _ _ body, countZero =>
      congrArg (composePath oneCell)
        (RawTwoCellExpr.sourcePath_eq_targetPath_of_generatorCount_zero body countZero)
  | _, _, _, _, @RawTwoCellExpr.whiskerRight _ _ _ _ _ _ oneCell body, countZero =>
      congrArg (fun boundaryPath => composePath boundaryPath oneCell)
        (RawTwoCellExpr.sourcePath_eq_targetPath_of_generatorCount_zero body countZero)

/-- A generator-free 2-cell expression contributes NOTHING to the spine: its difference-list is
transparent for every boundary accumulator. -/
theorem RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    cell.generatorCount = 0 →
    cell.spineDiff leftAccumulator rightAccumulator rest = rest
  | _, _, _, _, _, _, .gen _, _, countEq => absurd countEq (natSuccNeZero 0)
  | _, _, _, _, _, _, .id _, _, _ => rfl
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, rest,
      countZero => by
      dsimp only [RawTwoCellExpr.generatorCount] at countZero
      have alphaZero : cellAlpha.generatorCount = 0 := by
        cases alphaProbe : cellAlpha.generatorCount with
        | zero => rfl
        | succ predecessorCount =>
            rw [alphaProbe, Nat.succ_add] at countZero
            exact absurd countZero (natSuccNeZero _)
      have betaZero : cellBeta.generatorCount = 0 := by
        cases betaProbe : cellBeta.generatorCount with
        | zero => rfl
        | succ predecessorCount =>
            rw [betaProbe, Nat.add_succ] at countZero
            exact absurd countZero (natSuccNeZero _)
      dsimp only [RawTwoCellExpr.spineDiff]
      rw [RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAccumulator
        rightAccumulator cellBeta rest betaZero]
      exact RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAccumulator
        rightAccumulator cellAlpha rest alphaZero
  | _, _, leftAccumulator, rightAccumulator, _, _,
      @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell _ _ body, rest, countZero =>
      RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero
        (composePath leftAccumulator oneCell) rightAccumulator body rest countZero
  | _, _, leftAccumulator, rightAccumulator, _, _,
      @RawTwoCellExpr.whiskerRight _ _ _ _ _ _ oneCell body, rest, countZero =>
      RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAccumulator
        (composePath oneCell rightAccumulator) body rest countZero

/-! ## Production: a cell's spine difference-list is boundary-chained -/

/-- **Production.**  A cell's spine difference-list is chained from its SOURCE boundary whenever
the rest is chained from its TARGET boundary — each generator fires at the boundary its whisker
accumulators and source 1-cell describe, and vertical composition threads the middle boundary. -/
theorem spineBoundaryChained_spineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    SpineBoundaryChained (leftAccumulator.length + localCod.length + rightAccumulator.length)
      rest →
    SpineBoundaryChained (leftAccumulator.length + localDom.length + rightAccumulator.length)
      (cell.spineDiff leftAccumulator rightAccumulator rest)
  | _, _, leftAccumulator, rightAccumulator, _, _, .gen generator, rest, restChained => by
      dsimp only [RawTwoCellExpr.spineDiff]
      exact SpineBoundaryChained.cons _ rfl restChained
  | _, _, _, _, _, _, .id _, _, restChained => restChained
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, rest,
      restChained =>
      spineBoundaryChained_spineDiff leftAccumulator rightAccumulator cellAlpha
        (cellBeta.spineDiff leftAccumulator rightAccumulator rest)
        (spineBoundaryChained_spineDiff leftAccumulator rightAccumulator cellBeta rest
          restChained)
  | _, _, leftAccumulator, rightAccumulator, _, _,
      @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell bodySourcePath bodyTargetPath body, rest,
      restChained => by
      dsimp only [RawTwoCellExpr.spineDiff]
      have restChainedShifted : SpineBoundaryChained
          ((composePath leftAccumulator oneCell).length + bodyTargetPath.length
            + rightAccumulator.length) rest := by
        rw [ModalityPath.length_composePath leftAccumulator oneCell,
          Nat.add_assoc leftAccumulator.length oneCell.length bodyTargetPath.length,
          ← ModalityPath.length_composePath oneCell bodyTargetPath]
        exact restChained
      have producedShifted := spineBoundaryChained_spineDiff
        (composePath leftAccumulator oneCell) rightAccumulator body rest restChainedShifted
      rw [ModalityPath.length_composePath oneCell bodySourcePath,
        ← Nat.add_assoc leftAccumulator.length oneCell.length bodySourcePath.length,
        ← ModalityPath.length_composePath leftAccumulator oneCell]
      exact producedShifted
  | _, _, leftAccumulator, rightAccumulator, _, _,
      @RawTwoCellExpr.whiskerRight _ _ _ _ bodySourcePath bodyTargetPath oneCell body, rest,
      restChained => by
      dsimp only [RawTwoCellExpr.spineDiff]
      have restChainedShifted : SpineBoundaryChained
          (leftAccumulator.length + bodyTargetPath.length
            + (composePath oneCell rightAccumulator).length) rest := by
        rw [ModalityPath.length_composePath oneCell rightAccumulator,
          ← Nat.add_assoc (leftAccumulator.length + bodyTargetPath.length) oneCell.length
            rightAccumulator.length,
          Nat.add_assoc leftAccumulator.length bodyTargetPath.length oneCell.length,
          ← ModalityPath.length_composePath bodyTargetPath oneCell]
        exact restChained
      have producedShifted := spineBoundaryChained_spineDiff leftAccumulator
        (composePath oneCell rightAccumulator) body rest restChainedShifted
      rw [ModalityPath.length_composePath bodySourcePath oneCell,
        ← Nat.add_assoc leftAccumulator.length bodySourcePath.length oneCell.length,
        Nat.add_assoc (leftAccumulator.length + bodySourcePath.length) oneCell.length
          rightAccumulator.length,
        ← ModalityPath.length_composePath oneCell rightAccumulator]
      exact producedShifted

/-! ## Inversion: peeling a cell's spine contribution off a chain -/

/-- **Inversion.**  Peeling a cell's spine contribution off a chain at the cell's SOURCE boundary
leaves the rest chained at the cell's TARGET boundary — the converse of production, available
exactly when the chain boundary is the cell's own. -/
theorem spineBoundaryChained_rest_of_spineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    SpineBoundaryChained (leftAccumulator.length + localDom.length + rightAccumulator.length)
      (cell.spineDiff leftAccumulator rightAccumulator rest) →
    SpineBoundaryChained (leftAccumulator.length + localCod.length + rightAccumulator.length)
      rest
  | _, _, _, _, _, _, .gen _, rest, chained => by
      dsimp only [RawTwoCellExpr.spineDiff] at chained
      exact (spineBoundaryChained_tail chained).2
  | _, _, _, _, _, _, .id _, _, chained => chained
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, rest, chained =>
      spineBoundaryChained_rest_of_spineDiff leftAccumulator rightAccumulator cellBeta rest
        (spineBoundaryChained_rest_of_spineDiff leftAccumulator rightAccumulator cellAlpha
          (cellBeta.spineDiff leftAccumulator rightAccumulator rest) chained)
  | _, _, leftAccumulator, rightAccumulator, _, _,
      @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell bodySourcePath bodyTargetPath body, rest, chained => by
      have chainedShifted : SpineBoundaryChained
          ((composePath leftAccumulator oneCell).length + bodySourcePath.length
            + rightAccumulator.length)
          (body.spineDiff (composePath leftAccumulator oneCell) rightAccumulator rest) := by
        rw [ModalityPath.length_composePath leftAccumulator oneCell,
          Nat.add_assoc leftAccumulator.length oneCell.length bodySourcePath.length,
          ← ModalityPath.length_composePath oneCell bodySourcePath]
        exact chained
      have restShifted := spineBoundaryChained_rest_of_spineDiff
        (composePath leftAccumulator oneCell) rightAccumulator body rest chainedShifted
      rw [ModalityPath.length_composePath oneCell bodyTargetPath,
        ← Nat.add_assoc leftAccumulator.length oneCell.length bodyTargetPath.length,
        ← ModalityPath.length_composePath leftAccumulator oneCell]
      exact restShifted
  | _, _, leftAccumulator, rightAccumulator, _, _,
      @RawTwoCellExpr.whiskerRight _ _ _ _ bodySourcePath bodyTargetPath oneCell body, rest, chained => by
      have chainedShifted : SpineBoundaryChained
          (leftAccumulator.length + bodySourcePath.length
            + (composePath oneCell rightAccumulator).length)
          (body.spineDiff leftAccumulator (composePath oneCell rightAccumulator) rest) := by
        rw [ModalityPath.length_composePath oneCell rightAccumulator,
          ← Nat.add_assoc (leftAccumulator.length + bodySourcePath.length) oneCell.length
            rightAccumulator.length,
          Nat.add_assoc leftAccumulator.length bodySourcePath.length oneCell.length,
          ← ModalityPath.length_composePath bodySourcePath oneCell]
        exact chained
      have restShifted := spineBoundaryChained_rest_of_spineDiff leftAccumulator
        (composePath oneCell rightAccumulator) body rest chainedShifted
      rw [ModalityPath.length_composePath bodyTargetPath oneCell,
        ← Nat.add_assoc leftAccumulator.length bodyTargetPath.length oneCell.length,
        Nat.add_assoc (leftAccumulator.length + bodyTargetPath.length) oneCell.length
          rightAccumulator.length,
        ← ModalityPath.length_composePath oneCell rightAccumulator]
      exact restShifted

/-! ## Pinning: a generator-carrying cell forces the chain boundary -/

/-- **Pinning.**  A generator-carrying cell PINS the chain boundary: whenever its spine
difference-list is chained at some boundary, that boundary IS the cell's source-boundary width.
The first generator inside the cell fires at the cell's source boundary (generator-free prefixes
are boundary-silent by `sourcePath_eq_targetPath_of_generatorCount_zero`), and cons inversion
reads the boundary off it. -/
theorem spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} {boundaryLength : Nat} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    cell.generatorCount ≠ 0 →
    SpineBoundaryChained boundaryLength (cell.spineDiff leftAccumulator rightAccumulator rest) →
    leftAccumulator.length + localDom.length + rightAccumulator.length = boundaryLength
  | _, _, _, _, _, _, .gen _, rest, _, chained => by
      dsimp only [RawTwoCellExpr.spineDiff] at chained
      exact (spineBoundaryChained_tail chained).1
  | _, _, _, _, _, _, .id _, _, hasGenerator, _ => absurd rfl hasGenerator
  | _, _, leftAccumulator, rightAccumulator, _, _,
      .vcomp cellAlpha cellBeta, rest,
      hasGenerator, chained => by
      cases alphaProbe : cellAlpha.generatorCount with
      | succ predecessorCount =>
          exact spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero leftAccumulator
            rightAccumulator cellAlpha
            (cellBeta.spineDiff leftAccumulator rightAccumulator rest)
            (fun alphaZero => absurd (alphaProbe.symm.trans alphaZero)
              (natSuccNeZero predecessorCount))
            chained
      | zero =>
          have chainedUnfolded : SpineBoundaryChained boundaryLength
              (cellAlpha.spineDiff leftAccumulator rightAccumulator
                (cellBeta.spineDiff leftAccumulator rightAccumulator rest)) := chained
          have alphaTransparent := RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero
            leftAccumulator rightAccumulator cellAlpha
            (cellBeta.spineDiff leftAccumulator rightAccumulator rest) alphaProbe
          have chainedAtBeta : SpineBoundaryChained boundaryLength
              (cellBeta.spineDiff leftAccumulator rightAccumulator rest) :=
            alphaTransparent ▸ chainedUnfolded
          have betaNonZero : cellBeta.generatorCount ≠ 0 := fun betaZero =>
            hasGenerator (show cellAlpha.generatorCount + cellBeta.generatorCount = 0 by
              rw [alphaProbe, betaZero])
          have pinnedAtMiddle := spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero
            leftAccumulator rightAccumulator cellBeta rest betaNonZero chainedAtBeta
          rw [RawTwoCellExpr.sourcePath_eq_targetPath_of_generatorCount_zero cellAlpha
            alphaProbe]
          exact pinnedAtMiddle
  | _, _, leftAccumulator, rightAccumulator, _, _,
      @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell bodySourcePath _ body, rest,
      hasGenerator, chained => by
      have pinnedShifted := spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero
        (composePath leftAccumulator oneCell) rightAccumulator body rest hasGenerator chained
      rw [ModalityPath.length_composePath oneCell bodySourcePath,
        ← Nat.add_assoc leftAccumulator.length oneCell.length bodySourcePath.length,
        ← ModalityPath.length_composePath leftAccumulator oneCell]
      exact pinnedShifted
  | _, _, leftAccumulator, rightAccumulator, _, _,
      @RawTwoCellExpr.whiskerRight _ _ _ _ bodySourcePath _ oneCell body, rest,
      hasGenerator, chained => by
      have pinnedShifted := spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero
        leftAccumulator (composePath oneCell rightAccumulator) body rest hasGenerator chained
      rw [ModalityPath.length_composePath bodySourcePath oneCell,
        ← Nat.add_assoc leftAccumulator.length bodySourcePath.length oneCell.length,
        Nat.add_assoc (leftAccumulator.length + bodySourcePath.length) oneCell.length
          rightAccumulator.length,
        ← ModalityPath.length_composePath oneCell rightAccumulator]
      exact pinnedShifted

/-! ## The initial-state seed -/

/-- Every cell's spine is chained from its source 1-cell's length — the boundary invariant holds
at the empty-accumulator flattening the soundness capstone starts from. -/
theorem RawTwoCellExpr.spineBoundaryChained_spine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    SpineBoundaryChained sourcePath.length cell.spine := by
  have chainedPadded := spineBoundaryChained_spineDiff (identityPath sourceMode)
    (identityPath targetMode) cell [] (SpineBoundaryChained.nil _)
  have boundaryCollapses : (identityPath (graph := signature.graph) sourceMode).length
      + sourcePath.length + (identityPath (graph := signature.graph) targetMode).length
      = sourcePath.length := by
    dsimp only [identityPath, ModalityPath.length]
    rw [Nat.add_zero, Nat.zero_add]
  exact boundaryCollapses ▸ chainedPadded

/-! ## Honesty marker -/

/-- **Honesty marker — the spine boundary-chain substrate is SHIPPED.**  Boundary widths
(`SpineAtom.domBoundaryLength` / `codBoundaryLength`), the chain discipline
(`SpineBoundaryChained` + cons inversion), boundary-silence of generator-free cells, production
(`spineBoundaryChained_spineDiff`), inversion (`spineBoundaryChained_rest_of_spineDiff`),
pinning (`spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero`), and the initial-state
seed (`RawTwoCellExpr.spineBoundaryChained_spine`).  NOT yet covered: the Godement-nest window
bound + chain preservation, and threading the invariant through the conditioned trace induction
to discharge the unconditional core swap — the next bricks of the in-range discipline.
`= true`. -/
def fxMode_hasSpineBoundaryChainSubstrate : Bool := true

end FX1Poly.Polygraph
