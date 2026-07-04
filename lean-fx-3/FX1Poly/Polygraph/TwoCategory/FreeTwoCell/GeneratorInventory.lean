import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # GeneratorInventory — the packed-generator inventory is a class invariant (FREE-7)

First invariance brick of the BOUNDED-ATOM-UNIVERSE route (the corrected FREE-7 endgame
after the tag-order falsification): swaps re-whisker atoms but never touch WHICH
generator an atom carries, so the list of packed generator occurrences is preserved up
to head transpositions — in particular every atom of every class member draws its
generator from the SEED's finite inventory.

  * `PackedSpineGenerator` / `SpineAtom.packedGenerator` — a generator occurrence with
    its mid-modes and boundary 1-cells, detached from the whisker contexts (the part of
    an atom a swap can never change);
  * `spinePackedGenerators` — the trace's occurrence inventory (cons-only);
  * `listMemSwapHeadsIff` / `listMemConsCongrIff` — the two zero-axiom membership
    movers (head transposition, shared-head congruence);
  * ★ `AtomicTraceEquiv.packedGeneratorMemIff` — inventory membership is invariant
    across the whole trace equivalence;
  * `packedGenerator_memOfSeed_ofTraceEquiv` — the universe-facing corollary: an atom of
    a class member carries a seed generator.

Downstream: the atom universe `U` ranges its generator component over
`spinePackedGenerators seed` — a finite list — with the letter and width bounds
supplied by the companion invariance bricks.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The packed generator occurrence -/

/-- A generator occurrence packaged with its mid-modes and boundary 1-cells — everything
about an atom EXCEPT the whisker contexts.  Swaps re-whisker; they never change this. -/
structure PackedSpineGenerator (signature : ModeSignature) where
  /-- The mode at the generator's left edge. -/
  generatorSourceMode : signature.graph.Mode
  /-- The mode at the generator's right edge. -/
  generatorTargetMode : signature.graph.Mode
  /-- The generator's source 1-cell. -/
  generatorDom : ModalityPath signature.graph generatorSourceMode generatorTargetMode
  /-- The generator's target 1-cell. -/
  generatorCod : ModalityPath signature.graph generatorSourceMode generatorTargetMode
  /-- The generating 2-cell itself. -/
  generator : signature.twoCell generatorDom generatorCod

/-- Project an atom's packed generator occurrence (drop the whisker contexts). -/
def SpineAtom.packedGenerator {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) : PackedSpineGenerator signature :=
  ⟨atom.leftMidMode, atom.rightMidMode, atom.generatorDom, atom.generatorCod,
    atom.generator⟩

/-- The trace's occurrence inventory (cons-only recursion). -/
def spinePackedGenerators {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    List (SpineAtom signature sourceMode targetMode) →
    List (PackedSpineGenerator signature)
  | [] => []
  | atom :: rest => atom.packedGenerator :: spinePackedGenerators rest

/-- An atom's packed generator is in its trace's inventory. -/
theorem spinePackedGenerators_containsAtomGenerator {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {trace : List (SpineAtom signature sourceMode targetMode)}
    {atom : SpineAtom signature sourceMode targetMode} (atomMem : atom ∈ trace) :
    atom.packedGenerator ∈ spinePackedGenerators trace := by
  induction atomMem with
  | head rest => exact List.Mem.head (spinePackedGenerators rest)
  | tail headAtom _innerMem innerHypothesis => exact List.Mem.tail _ innerHypothesis

/-! ## The two membership movers -/

/-- Membership is blind to a head transposition. -/
theorem listMemSwapHeadsIff {elementType : Type} (firstHead secondHead : elementType)
    (rest : List elementType) (element : elementType) :
    element ∈ firstHead :: secondHead :: rest
      ↔ element ∈ secondHead :: firstHead :: rest := by
  constructor
  all_goals
    intro elementMem
    cases elementMem with
    | head => exact List.Mem.tail _ (List.Mem.head rest)
    | tail _ innerMem =>
        cases innerMem with
        | head => exact List.Mem.head _
        | tail _ deepMem => exact List.Mem.tail _ (List.Mem.tail _ deepMem)

/-- Membership congruence under a shared head. -/
theorem listMemConsCongrIff {elementType : Type} (sharedHead : elementType)
    {firstRest secondRest : List elementType} (element : elementType)
    (restIff : element ∈ firstRest ↔ element ∈ secondRest) :
    element ∈ sharedHead :: firstRest ↔ element ∈ sharedHead :: secondRest := by
  constructor
  · intro elementMem
    cases elementMem with
    | head => exact List.Mem.head secondRest
    | tail _ innerMem => exact List.Mem.tail _ (restIff.mp innerMem)
  · intro elementMem
    cases elementMem with
    | head => exact List.Mem.head firstRest
    | tail _ innerMem => exact List.Mem.tail _ (restIff.mpr innerMem)

/-! ## ★ The inventory invariance -/

/-- ★ **Inventory membership is a class invariant**: a swap transposes the two head
occurrences and fixes everything else, so membership in the packed-generator inventory
transfers across the whole trace equivalence. -/
theorem AtomicTraceEquiv.packedGeneratorMemIff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv signature firstList secondList)
    (packedGen : PackedSpineGenerator signature) :
    packedGen ∈ spinePackedGenerators firstList
      ↔ packedGen ∈ spinePackedGenerators secondList := by
  induction traceEquiv with
  | ofSwap swapStep =>
      cases swapStep with
      | @swap _swapSourceMode _swapMiddleLeft _swapMiddleRight _swapTargetMode _oneCellFMid
          _oneCellFHigh _oneCellGLow _oneCellGMid generatorLeft generatorRight leftAcc
          inertPath rightAcc rest =>
          exact listMemSwapHeadsIff _ _ (spinePackedGenerators rest) packedGen
  | refl _ => exact Iff.rfl
  | symm _ innerHypothesis => exact innerHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis
  | consCongr atom _ innerHypothesis =>
      exact listMemConsCongrIff atom.packedGenerator packedGen innerHypothesis

/-- The universe-facing corollary: every atom of a class member draws its generator from
the seed's finite inventory. -/
theorem packedGenerator_memOfSeed_ofTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {seedTrace memberTrace : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv signature seedTrace memberTrace)
    {atom : SpineAtom signature overallSource overallTarget}
    (atomMem : atom ∈ memberTrace) :
    atom.packedGenerator ∈ spinePackedGenerators seedTrace :=
  (traceEquiv.packedGeneratorMemIff atom.packedGenerator).mpr
    (spinePackedGenerators_containsAtomGenerator atomMem)

end FX1Poly.Polygraph
