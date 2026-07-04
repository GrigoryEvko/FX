import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineGodement

/-! # AtomicSwap — the atom-level adjacent transposition + its closure (FREE-5 scaffold)

The trace decision works at ATOM granularity: two adjacent, horizontally-independent atoms
transpose with context shifts.  This file ships the data layer and the easy inclusion:

  * `SpineAtomSwap` — the single-constructor adjacent swap, carrying an explicit INERT middle
    zone between the two generators' columns (the zone a whisker interposes; the plain
    adjacent swap is the `identityPath` instance, definitionally, since identity paths
    compose away on the left).  The contexts are written in exactly the association the
    `godement` constructor produces, so the embedding below is definitional;
  * `SpineAtomSwap.toGodementStep` — every atomic swap IS a Godement block step at singleton
    blocks (`id` outer cells, `gen` moving block, `whiskerLeft inert (gen _)` passive block);
  * `AtomicTraceEquiv` — the reflexive-symmetric-transitive-cons closure of the atomic swap;
  * `AtomicTraceEquiv.toSpineTraceEquiv` — the atomic closure includes into the block-level
    trace equivalence (each swap via the embedding, closure operators map one-to-one);
  * `AtomicTraceEquiv.castList` — transport along list equalities (the reassociation
    transports the generation theorem's whisker arms need);
  * `AtomicTraceEquiv.prependSpineDiff` — an arbitrary cell's spine difference-list prepends
    (the shared-prefix congruence, mirroring `SpineTraceEquiv.prependSpineDiff`).

STILL OPEN (the FREE-5 content, tracked by the marker): the GENERATION theorem — every
block-level `SpineGodementStep` is in `AtomicTraceEquiv` (double induction over the two
blocks, reassociation transports at the whisker arms), whence the two closures coincide.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The atomic swap -/

/-- **The atom-level adjacent transposition**: a generator atom in the LEFT column moves past
a generator atom in the RIGHT column, separated by an INERT middle zone; the left atom's
right context tracks the right generator's state (`gLow ↝ gMid`) and the right atom's left
context tracks the left generator's state (`fHigh ↝ fMid`).  The contexts are associated
exactly as the `godement` constructor at singleton blocks produces them
(`toGodementStep` is definitional); the plain adjacent swap is `inertPath := identityPath`
(also definitional — identity paths compose away on the left). -/
inductive SpineAtomSwap (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} :
    List (SpineAtom signature overallSource overallTarget) →
    List (SpineAtom signature overallSource overallTarget) → Prop where
  /-- Transpose two adjacent horizontally-independent generator atoms. -/
  | swap {swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode : signature.graph.Mode}
      {oneCellFMid oneCellFHigh : ModalityPath signature.graph swapSourceMode swapMiddleLeft}
      {oneCellGLow oneCellGMid : ModalityPath signature.graph swapMiddleRight swapTargetMode}
      (generatorLeft : signature.twoCell oneCellFMid oneCellFHigh)
      (generatorRight : signature.twoCell oneCellGLow oneCellGMid)
      (leftAcc : ModalityPath signature.graph overallSource swapSourceMode)
      (inertPath : ModalityPath signature.graph swapMiddleLeft swapMiddleRight)
      (rightAcc : ModalityPath signature.graph swapTargetMode overallTarget)
      (rest : List (SpineAtom signature overallSource overallTarget)) :
      SpineAtomSwap signature
        (⟨_, _, leftAcc, _, _, generatorLeft,
            composePath (composePath inertPath oneCellGLow) rightAcc⟩ ::
          ⟨_, _, composePath (composePath leftAcc oneCellFHigh) inertPath, _, _,
            generatorRight, rightAcc⟩ :: rest)
        (⟨_, _, composePath (composePath leftAcc oneCellFMid) inertPath, _, _,
            generatorRight, rightAcc⟩ ::
          ⟨_, _, leftAcc, _, _, generatorLeft,
            composePath (composePath inertPath oneCellGMid) rightAcc⟩ :: rest)

/-- Every atomic swap IS a Godement block step — at singleton blocks: identity outer cells,
the moving block a bare generator, the passive block the inert-whiskered generator.  The
list shapes coincide definitionally. -/
theorem SpineAtomSwap.toGodementStep {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (swapStep : SpineAtomSwap signature firstList secondList) :
    SpineGodementStep signature firstList secondList := by
  cases swapStep with
  | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode oneCellFMid
      oneCellFHigh oneCellGLow oneCellGMid generatorLeft generatorRight leftAcc inertPath
      rightAcc rest =>
      exact SpineGodementStep.godement
        (RawTwoCellExpr.id oneCellFMid)
        (RawTwoCellExpr.gen generatorLeft)
        (RawTwoCellExpr.whiskerLeft inertPath (RawTwoCellExpr.gen generatorRight))
        (RawTwoCellExpr.id (composePath inertPath oneCellGMid))
        leftAcc rightAcc rest

/-! ## The atomic closure -/

/-- **The atomic trace equivalence** — the reflexive-symmetric-transitive closure of the
adjacent atom swap, plus the head-cons congruence.  The FREE-5 generation theorem (open,
see the marker) identifies it with the block-level `SpineTraceEquiv`. -/
inductive AtomicTraceEquiv (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} :
    List (SpineAtom signature overallSource overallTarget) →
    List (SpineAtom signature overallSource overallTarget) → Prop where
  /-- A single adjacent atom swap. -/
  | ofSwap {firstList secondList : List (SpineAtom signature overallSource overallTarget)} :
      SpineAtomSwap signature firstList secondList →
      AtomicTraceEquiv signature firstList secondList
  /-- Reflexivity. -/
  | refl (spineList : List (SpineAtom signature overallSource overallTarget)) :
      AtomicTraceEquiv signature spineList spineList
  /-- Symmetry. -/
  | symm {firstList secondList : List (SpineAtom signature overallSource overallTarget)} :
      AtomicTraceEquiv signature firstList secondList →
      AtomicTraceEquiv signature secondList firstList
  /-- Transitivity. -/
  | trans {firstList secondList thirdList :
      List (SpineAtom signature overallSource overallTarget)} :
      AtomicTraceEquiv signature firstList secondList →
      AtomicTraceEquiv signature secondList thirdList →
      AtomicTraceEquiv signature firstList thirdList
  /-- A head atom passes through (independent prefix). -/
  | consCongr (atom : SpineAtom signature overallSource overallTarget)
      {firstList secondList : List (SpineAtom signature overallSource overallTarget)} :
      AtomicTraceEquiv signature firstList secondList →
      AtomicTraceEquiv signature (atom :: firstList) (atom :: secondList)

/-- The atomic closure INCLUDES into the block-level trace equivalence: each swap is a
Godement step, and the closure operators map one-to-one. -/
theorem AtomicTraceEquiv.toSpineTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (atomicEquiv : AtomicTraceEquiv signature firstList secondList) :
    SpineTraceEquiv signature firstList secondList := by
  induction atomicEquiv with
  | ofSwap swapStep => exact SpineTraceEquiv.ofStep swapStep.toGodementStep
  | refl spineList => exact SpineTraceEquiv.refl spineList
  | symm _ innerHypothesis => exact SpineTraceEquiv.symm innerHypothesis
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis
  | consCongr atom _ innerHypothesis => exact SpineTraceEquiv.consCongr atom innerHypothesis

/-! ## Transport + the prefix congruence -/

/-- Transport the atomic equivalence along list equalities — the reassociation transports the
generation theorem's whisker arms perform (atoms differing only in context association are
propositionally equal, hence so are the lists). -/
theorem AtomicTraceEquiv.castList {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList firstList' secondList' :
      List (SpineAtom signature overallSource overallTarget)}
    (firstEq : firstList = firstList') (secondEq : secondList = secondList')
    (atomicEquiv : AtomicTraceEquiv signature firstList secondList) :
    AtomicTraceEquiv signature firstList' secondList' :=
  firstEq ▸ secondEq ▸ atomicEquiv

/-- Prepending any cell's spine difference-list preserves the ATOMIC equivalence — the
shared-prefix congruence, mirroring `SpineTraceEquiv.prependSpineDiff` arm for arm. -/
theorem AtomicTraceEquiv.prependSpineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)} →
    AtomicTraceEquiv signature firstList secondList →
    AtomicTraceEquiv signature (cell.spineDiff leftAcc rightAcc firstList)
      (cell.spineDiff leftAcc rightAcc secondList)
  | _, _, leftAcc, rightAcc, _, _, .gen generator, _, _, atomicEquiv =>
      AtomicTraceEquiv.consCongr ⟨_, _, leftAcc, _, _, generator, rightAcc⟩ atomicEquiv
  | _, _, _, _, _, _, .id _, _, _, atomicEquiv => atomicEquiv
  | _, _, leftAcc, rightAcc, _, _, .vcomp cellLeft cellRight, _, _, atomicEquiv =>
      AtomicTraceEquiv.prependSpineDiff leftAcc rightAcc cellLeft
        (AtomicTraceEquiv.prependSpineDiff leftAcc rightAcc cellRight atomicEquiv)
  | _, _, leftAcc, rightAcc, _, _, .whiskerLeft oneCell body, _, _, atomicEquiv =>
      AtomicTraceEquiv.prependSpineDiff (composePath leftAcc oneCell) rightAcc body
        atomicEquiv
  | _, _, leftAcc, rightAcc, _, _, .whiskerRight oneCell body, _, _, atomicEquiv =>
      AtomicTraceEquiv.prependSpineDiff leftAcc (composePath oneCell rightAcc) body
        atomicEquiv

/-! ## Honesty marker -/

/-- **Honesty marker — the GENERATION theorem is PROVED.**  Shipped: the atomic swap data
layer with its definitional Godement embedding (`toGodementStep`), the atomic closure with
its inclusion (`toSpineTraceEquiv`), the atom move lemma
(`AtomicTraceEquiv.moveGeneratorPastCell`, `AtomicMove.lean`), the block move
(`AtomicTraceEquiv.blockMovePastCell`), the Godement step's atomicity
(`SpineGodementStep.toAtomicTraceEquiv`), and the closure identification
`spineTraceEquiv_iff_atomicTraceEquiv` (`AtomicSwapGeneration.lean`):
`SpineTraceEquiv = AtomicTraceEquiv`, so the trace decision may work at ATOM granularity.
Still open downstream (FREE-6/FREE-7): the oriented swap normal form and the decision
itself — `fxMode_hasDecidableTwoCellEquality` stays false until then. -/
def fxMode_hasAtomicSwapGeneration : Bool := true

end FX1Poly.Polygraph
