import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.BoundedPathEnumeration
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.GeneratorInventory
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TraceLetterInventoryBuilder
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.WidthBudget

/-! # AtomUniverse — the finite atom universe of a chained seed (FREE-7)

The universe product: candidate atoms are (packed generator from the seed's inventory)
× (bounded left context) × (bounded right context).  No transport is needed anywhere —
the packed generator's edge modes ARE the candidate's mid modes definitionally, and an
atom rebuilt from its own packed generator and contexts is the atom by structure eta.

  * `atomCandidatesOverLefts` — one generator, all left contexts × all right contexts;
  * `atomCandidatesForGenerator` — plug in the two bounded path enumerations;
  * `atomUniverse` — fold over the generator inventory;
  * `atomCandidatesOverLefts_containsMk` / `atomUniverse_containsAtom` — the two
    membership layers (induction on the respective list membership);
  * ★ `memberAtom_mem_atomUniverse` — **the universe is complete**: every atom of every
    class member of a boundary-chained seed is in the seed's computable atom universe
    (generator inventory leg B, letter-alphabet legs C+E1, width legs D+E2 composed).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The universe product -/

/-- All atoms wearing one packed generator: every left context crossed with every
right context (the packed edge modes are the mid modes — no transport). -/
def atomCandidatesOverLefts {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (packedGen : PackedSpineGenerator signature) :
    List (ModalityPath signature.graph sourceMode packedGen.generatorSourceMode) →
    (rightList : List (ModalityPath signature.graph packedGen.generatorTargetMode
      targetMode)) →
    List (SpineAtom signature sourceMode targetMode)
  | [], _rightList => []
  | leftContext :: remainingLefts, rightList =>
      rightList.map (fun rightContext =>
        ⟨packedGen.generatorSourceMode, packedGen.generatorTargetMode, leftContext,
          packedGen.generatorDom, packedGen.generatorCod, packedGen.generator,
          rightContext⟩)
        ++ atomCandidatesOverLefts packedGen remainingLefts rightList

/-- All atoms wearing one packed generator with contexts drawn from the bounded
inventory-lettered enumeration. -/
def atomCandidatesForGenerator {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (letterInventory : List (PackedModality signature.graph))
    (contextLengthBound : Nat) (sourceMode targetMode : signature.graph.Mode)
    (packedGen : PackedSpineGenerator signature) :
    List (SpineAtom signature sourceMode targetMode) :=
  atomCandidatesOverLefts packedGen
    (enumeratePathsUpTo modeDecEq letterInventory contextLengthBound sourceMode
      packedGen.generatorSourceMode)
    (enumeratePathsUpTo modeDecEq letterInventory contextLengthBound
      packedGen.generatorTargetMode targetMode)

/-- The atom universe: candidates for every generator in the inventory. -/
def atomUniverse {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (letterInventory : List (PackedModality signature.graph))
    (contextLengthBound : Nat) (sourceMode targetMode : signature.graph.Mode) :
    List (PackedSpineGenerator signature) →
    List (SpineAtom signature sourceMode targetMode)
  | [] => []
  | packedGen :: remainingGens =>
      atomCandidatesForGenerator modeDecEq letterInventory contextLengthBound
          sourceMode targetMode packedGen
        ++ atomUniverse modeDecEq letterInventory contextLengthBound sourceMode
          targetMode remainingGens

/-! ## The membership layers -/

/-- A candidate built from enumerated contexts is among the generator's candidates. -/
theorem atomCandidatesOverLefts_containsMk {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {packedGen : PackedSpineGenerator signature}
    {leftContext : ModalityPath signature.graph sourceMode
      packedGen.generatorSourceMode}
    {rightContext : ModalityPath signature.graph packedGen.generatorTargetMode
      targetMode}
    {leftList : List (ModalityPath signature.graph sourceMode
      packedGen.generatorSourceMode)}
    {rightList : List (ModalityPath signature.graph packedGen.generatorTargetMode
      targetMode)}
    (leftMem : leftContext ∈ leftList) (rightMem : rightContext ∈ rightList) :
    (⟨packedGen.generatorSourceMode, packedGen.generatorTargetMode, leftContext,
      packedGen.generatorDom, packedGen.generatorCod, packedGen.generator,
      rightContext⟩ : SpineAtom signature sourceMode targetMode)
      ∈ atomCandidatesOverLefts packedGen leftList rightList := by
  induction leftMem with
  | head remainingLefts => exact listMemAppendOfLeft _ (listMemMapOfMem rightMem)
  | tail headLeft _leftMemTail innerHypothesis =>
      exact listMemAppendOfRight _ innerHypothesis

/-- An atom whose packed generator is in the inventory and whose contexts are
enumerated is in the universe: at the head, the atom rebuilt from its own packed
generator and contexts is the atom by structure eta. -/
theorem atomUniverse_containsAtom {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    {letterInventory : List (PackedModality signature.graph)}
    {contextLengthBound : Nat} {sourceMode targetMode : signature.graph.Mode}
    {genList : List (PackedSpineGenerator signature)}
    {atom : SpineAtom signature sourceMode targetMode}
    (genMem : atom.packedGenerator ∈ genList)
    (leftMem : atom.leftContext ∈ enumeratePathsUpTo modeDecEq letterInventory
      contextLengthBound sourceMode atom.leftMidMode)
    (rightMem : atom.rightContext ∈ enumeratePathsUpTo modeDecEq letterInventory
      contextLengthBound atom.rightMidMode targetMode) :
    atom ∈ atomUniverse modeDecEq letterInventory contextLengthBound sourceMode
      targetMode genList := by
  induction genMem with
  | head remainingGens =>
      exact listMemAppendOfLeft _ (atomCandidatesOverLefts_containsMk leftMem rightMem)
  | tail headGen _genMemTail innerHypothesis =>
      exact listMemAppendOfRight _ innerHypothesis

/-! ## ★ The universe is complete -/

/-- ★ **Every class-member atom is in the seed's computable atom universe**: the
generator rides the class (leg B), the letters stay inside the seed's alphabet
(legs C + E1), and the context lengths stay inside the seed's width budget
(legs D + E2). -/
theorem memberAtom_mem_atomUniverse {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    {overallSource overallTarget : signature.graph.Mode}
    {seedTrace memberTrace : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv signature seedTrace memberTrace)
    {boundaryLength : Nat}
    (seedChained : SpineBoundaryChained boundaryLength seedTrace)
    {atom : SpineAtom signature overallSource overallTarget}
    (atomMem : atom ∈ memberTrace) :
    atom ∈ atomUniverse modeDecEq (traceLetterInventory seedTrace)
      (boundaryLength + traceGrowthBudget seedTrace) overallSource overallTarget
      (spinePackedGenerators seedTrace) := by
  have atomUses := memberAtomUsesOnly_seedInventory traceEquiv atomMem
  have widthBound := memberAtomWidth_bounded_ofSeed traceEquiv seedChained atomMem
  exact atomUniverse_containsAtom modeDecEq
    (packedGenerator_memOfSeed_ofTraceEquiv traceEquiv atomMem)
    (enumeratePathsUpTo_containsPath modeDecEq atom.leftContext
      atomUses.leftContextUsesOnly _
      (Nat.le_trans atom.leftContextLength_le_domBoundaryLength widthBound))
    (enumeratePathsUpTo_containsPath modeDecEq atom.rightContext
      atomUses.rightContextUsesOnly _
      (Nat.le_trans atom.rightContextLength_le_domBoundaryLength widthBound))

end FX1Poly.Polygraph
