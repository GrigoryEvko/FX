import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # SpinePathChain — the path-level chain discipline is a trace-class invariant

The ungated free-trace decision (the Mazurkiewicz occurrence-tracking route) reconstructs a
trace from its occurrence-tag order, and the reconstruction leans on CHAINING: every atom
fires exactly at the running 1-cell boundary PATH (not merely at its width) and hands its
target boundary path to the tail.  This file ships the invariant's foundation rung:

  * `SpineAtom.domBoundaryPath` / `SpineAtom.codBoundaryPath` — the atom's full source/target
    boundary 1-cells (left context, then the generator boundary, then the right context) —
    the path-level refinement of the shipped `domBoundaryLength`/`codBoundaryLength`;
  * `SpinePathChained` — the path-level chain discipline on atom lists, with cons inversion
    (`spinePathChained_tail`), mirroring the shipped width-level `SpineBoundaryChained`;
  * `composePath_middleAssoc` — the four-factor reassociation every swap-side goal reduces to
    (`((P·M)·S)·X = P·((M·S)·X)`, three `composePath_assoc` rewrites);
  * ★ `SpineAtomSwap.preservesPathChain` / `SpineAtomSwap.reflectsPathChain` — one adjacent
    atomic swap preserves chaining in BOTH directions: the redex pair's cross-atom handoff and
    the reduct pair's are the same path up to reassociation, so the running boundary and the
    tail handoff survive the transposition unchanged;
  * ★ `AtomicTraceEquiv.pathChainedTransfer` — chaining is a CLASS invariant of the whole
    atomic trace equivalence (both directions carried simultaneously through the symmetric
    closure, the boundary kept universally quantified in the conclusion so the cons-congruence
    arm can instantiate it at the head's target boundary).

The next rung tags atoms with occurrence indices and shows the tag order of a chained trace
determines the trace — chaining is what forces the whisker contexts.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Boundary paths + the chain discipline -/

/-- The full SOURCE boundary 1-cell at which an atom fires: left whisker context, then the
generator's source 1-cell, then the right whisker context. -/
def SpineAtom.domBoundaryPath {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) :
    ModalityPath signature.graph sourceMode targetMode :=
  composePath (composePath atom.leftContext atom.generatorDom) atom.rightContext

/-- The full TARGET boundary 1-cell an atom leaves behind: left whisker context, then the
generator's target 1-cell, then the right whisker context. -/
def SpineAtom.codBoundaryPath {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) :
    ModalityPath signature.graph sourceMode targetMode :=
  composePath (composePath atom.leftContext atom.generatorCod) atom.rightContext

/-- The path-level chain discipline on spine-atom lists: every atom fires exactly at the
running boundary 1-cell and hands its target boundary 1-cell to the tail.  The empty list is
chained at any boundary (it constrains nothing). -/
inductive SpinePathChained {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    ModalityPath signature.graph sourceMode targetMode →
    List (SpineAtom signature sourceMode targetMode) → Prop where
  /-- The empty spine is chained at any boundary. -/
  | nil (boundaryPath : ModalityPath signature.graph sourceMode targetMode) :
      SpinePathChained boundaryPath []
  /-- A cons is chained when the head fires at the running boundary and the tail is chained
  at the head's target boundary. -/
  | cons {boundaryPath : ModalityPath signature.graph sourceMode targetMode}
      (atom : SpineAtom signature sourceMode targetMode)
      {rest : List (SpineAtom signature sourceMode targetMode)}
      (headFiresAtBoundary : atom.domBoundaryPath = boundaryPath)
      (tailChained : SpinePathChained atom.codBoundaryPath rest) :
      SpinePathChained boundaryPath (atom :: rest)

/-- Cons inversion for the path-level chain: the head fires at the running boundary and the
tail is chained at the head's target boundary. -/
theorem spinePathChained_tail {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {boundaryPath : ModalityPath signature.graph sourceMode targetMode}
    {atom : SpineAtom signature sourceMode targetMode}
    {rest : List (SpineAtom signature sourceMode targetMode)}
    (chained : SpinePathChained boundaryPath (atom :: rest)) :
    atom.domBoundaryPath = boundaryPath ∧ SpinePathChained atom.codBoundaryPath rest := by
  cases chained with
  | cons _ headFiresAtBoundary tailChained => exact ⟨headFiresAtBoundary, tailChained⟩

/-! ## The four-factor reassociation -/

/-- The reassociation every swap-side chain goal reduces to: pulling the whisker prefix out of
a left-nested four-factor composite.  Three `composePath_assoc` rewrites. -/
theorem composePath_middleAssoc {graph : ModeGraph}
    {startMode prefixEndMode middleEndMode segmentEndMode finishMode : graph.Mode}
    (prefixPath : ModalityPath graph startMode prefixEndMode)
    (middlePath : ModalityPath graph prefixEndMode middleEndMode)
    (segmentPath : ModalityPath graph middleEndMode segmentEndMode)
    (suffixPath : ModalityPath graph segmentEndMode finishMode) :
    composePath (composePath (composePath prefixPath middlePath) segmentPath) suffixPath
      = composePath prefixPath (composePath (composePath middlePath segmentPath) suffixPath) := by
  rw [composePath_assoc, composePath_assoc, composePath_assoc]

/-! ## One swap preserves chaining, in both directions -/

/-- ★ **Swap preservation (forward)**: an adjacent atomic swap sends a chained trace to a
chained trace at the same boundary.  The reduct pair's internal handoff and its tail handoff
are the redex's up to `composePath_middleAssoc`. -/
theorem SpineAtomSwap.preservesPathChain {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    {boundaryPath : ModalityPath signature.graph overallSource overallTarget}
    (swapStep : SpineAtomSwap signature firstList secondList)
    (chained : SpinePathChained boundaryPath firstList) :
    SpinePathChained boundaryPath secondList := by
  cases swapStep with
  | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode oneCellFMid
      oneCellFHigh oneCellGLow oneCellGMid generatorLeft generatorRight leftAcc inertPath
      rightAcc rest =>
      obtain ⟨headFires, tailChained⟩ := spinePathChained_tail chained
      obtain ⟨_, restChained⟩ := spinePathChained_tail tailChained
      dsimp only [SpineAtom.domBoundaryPath, SpineAtom.codBoundaryPath]
        at headFires restChained
      refine SpinePathChained.cons _ ?movedFires (SpinePathChained.cons _ ?stayedFires ?tail)
      case movedFires =>
          dsimp only [SpineAtom.domBoundaryPath]
          rw [composePath_middleAssoc]
          exact headFires
      case stayedFires =>
          dsimp only [SpineAtom.domBoundaryPath, SpineAtom.codBoundaryPath]
          rw [composePath_middleAssoc]
      case tail =>
          dsimp only [SpineAtom.codBoundaryPath]
          exact composePath_middleAssoc (composePath leftAcc oneCellFHigh) inertPath
            oneCellGMid rightAcc ▸ restChained

/-- ★ **Swap preservation (backward)**: an adjacent atomic swap REFLECTS chaining — a chained
reduct trace has a chained redex trace at the same boundary.  Same reassociation bridges,
applied in the other direction (the swap relation itself is not symmetric: the moved atom
sits at the lower column only on the redex side). -/
theorem SpineAtomSwap.reflectsPathChain {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    {boundaryPath : ModalityPath signature.graph overallSource overallTarget}
    (swapStep : SpineAtomSwap signature firstList secondList)
    (chained : SpinePathChained boundaryPath secondList) :
    SpinePathChained boundaryPath firstList := by
  cases swapStep with
  | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode oneCellFMid
      oneCellFHigh oneCellGLow oneCellGMid generatorLeft generatorRight leftAcc inertPath
      rightAcc rest =>
      obtain ⟨headFires, tailChained⟩ := spinePathChained_tail chained
      obtain ⟨_, restChained⟩ := spinePathChained_tail tailChained
      dsimp only [SpineAtom.domBoundaryPath, SpineAtom.codBoundaryPath]
        at headFires restChained
      refine SpinePathChained.cons _ ?leftFires (SpinePathChained.cons _ ?rightFires ?tail)
      case leftFires =>
          dsimp only [SpineAtom.domBoundaryPath]
          rw [← composePath_middleAssoc]
          exact headFires
      case rightFires =>
          dsimp only [SpineAtom.domBoundaryPath, SpineAtom.codBoundaryPath]
          rw [composePath_middleAssoc]
      case tail =>
          dsimp only [SpineAtom.codBoundaryPath]
          exact (composePath_middleAssoc (composePath leftAcc oneCellFHigh) inertPath
            oneCellGMid rightAcc).symm ▸ restChained

/-! ## Chaining is a class invariant of the atomic trace equivalence -/

/-- ★ **The chain-transfer theorem**: path-level chaining transfers along the WHOLE atomic
trace equivalence, in both directions at every boundary.  Both directions ride together
through the symmetric closure; the boundary stays universally quantified in the conclusion so
the cons-congruence arm can instantiate the induction hypothesis at the head atom's target
boundary. -/
theorem AtomicTraceEquiv.pathChainedTransfer {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv signature firstList secondList) :
    ∀ (boundaryPath : ModalityPath signature.graph overallSource overallTarget),
      (SpinePathChained boundaryPath firstList → SpinePathChained boundaryPath secondList)
        ∧ (SpinePathChained boundaryPath secondList
            → SpinePathChained boundaryPath firstList) := by
  induction traceEquiv with
  | ofSwap swapStep =>
      exact fun _ => ⟨swapStep.preservesPathChain, swapStep.reflectsPathChain⟩
  | refl _ => exact fun _ => ⟨id, id⟩
  | symm _ innerHypothesis =>
      exact fun boundaryPath =>
        ⟨(innerHypothesis boundaryPath).2, (innerHypothesis boundaryPath).1⟩
  | trans _ _ firstHypothesis secondHypothesis =>
      exact fun boundaryPath =>
        ⟨fun chained => (secondHypothesis boundaryPath).1
            ((firstHypothesis boundaryPath).1 chained),
          fun chained => (firstHypothesis boundaryPath).2
            ((secondHypothesis boundaryPath).2 chained)⟩
  | consCongr atom _ innerHypothesis =>
      refine fun boundaryPath => ⟨fun chained => ?forward, fun chained => ?backward⟩
      case forward =>
          obtain ⟨headFires, tailChained⟩ := spinePathChained_tail chained
          exact SpinePathChained.cons atom headFires
            ((innerHypothesis atom.codBoundaryPath).1 tailChained)
      case backward =>
          obtain ⟨headFires, tailChained⟩ := spinePathChained_tail chained
          exact SpinePathChained.cons atom headFires
            ((innerHypothesis atom.codBoundaryPath).2 tailChained)

end FX1Poly.Polygraph
