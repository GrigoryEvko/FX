import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.LetterInventory
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ExtractionMembership

/-! # TraceLetterInventoryBuilder — the seed's own letter alphabet (FREE-7)

The letter invariance (`LetterInventory.lean`) holds for ANY inventory covering the
seed; this brick builds the CANONICAL one — the finite list of exactly the letters the
seed's atoms use — and proves the seed covers itself.  Combined with the invariance,
every atom of every class member draws its letters from this computable list: the
alphabet leg of the atom universe becomes concrete.

  * `pathLetters` / `atomLetters` / `traceLetterInventory` — collect the letters of a
    path, an atom (contexts AND generator boundaries), a trace (cons/append-only);
  * `pathUsesOnly_monotone` / `atomUsesOnly_monotone` / `traceUsesOnly_monotone` — the
    disciplines are monotone in the inventory;
  * `pathUsesOnly_ownLetters` / `atomUsesOnly_ownLetters` — self-containment per path
    and per atom (each block of the four-block append covers its own field);
  * ★ `traceUsesOnly_ownInventory` — the seed obeys its own inventory;
  * ★ `memberAtomUsesOnly_seedInventory` — the concrete universe-facing fact: every
    atom of every class member uses only `traceLetterInventory seed`.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Collecting the letters -/

/-- The letters of a path, packaged (cons-only recursion). -/
def pathLetters {graph : ModeGraph} :
    {sourceMode targetMode : graph.Mode} →
    ModalityPath graph sourceMode targetMode → List (PackedModality graph)
  | _, _, ModalityPath.nil _ => []
  | _, _, ModalityPath.cons edgeModality rest =>
      (⟨_, _, edgeModality⟩ : PackedModality graph) :: pathLetters rest

/-- The letters of an atom: left context, generator source, generator target, right
context — four appended blocks. -/
def atomLetters {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) :
    List (PackedModality signature.graph) :=
  pathLetters atom.leftContext
    ++ (pathLetters atom.generatorDom
      ++ (pathLetters atom.generatorCod ++ pathLetters atom.rightContext))

/-- The trace's letter inventory (append of the atoms' blocks). -/
def traceLetterInventory {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    List (SpineAtom signature sourceMode targetMode) →
    List (PackedModality signature.graph)
  | [] => []
  | atom :: rest => atomLetters atom ++ traceLetterInventory rest

/-! ## The disciplines are monotone in the inventory -/

/-- Growing the inventory preserves a path's letter discipline. -/
theorem pathUsesOnly_monotone {graph : ModeGraph}
    {smallList bigList : List (PackedModality graph)}
    (isCovered : ∀ edgeEntry, edgeEntry ∈ smallList → edgeEntry ∈ bigList) :
    {sourceMode targetMode : graph.Mode} →
    (path : ModalityPath graph sourceMode targetMode) →
    pathUsesOnly smallList path → pathUsesOnly bigList path
  | _, _, ModalityPath.nil _, _pathUses => True.intro
  | _, _, ModalityPath.cons _edgeModality rest, pathUses =>
      ⟨isCovered _ pathUses.1, pathUsesOnly_monotone isCovered rest pathUses.2⟩

/-- Growing the inventory preserves an atom's letter discipline. -/
theorem atomUsesOnly_monotone {signature : ModeSignature}
    {smallList bigList : List (PackedModality signature.graph)}
    (isCovered : ∀ edgeEntry, edgeEntry ∈ smallList → edgeEntry ∈ bigList)
    {sourceMode targetMode : signature.graph.Mode}
    {atom : SpineAtom signature sourceMode targetMode}
    (atomUses : AtomUsesOnly smallList atom) : AtomUsesOnly bigList atom where
  leftContextUsesOnly :=
    pathUsesOnly_monotone isCovered atom.leftContext atomUses.leftContextUsesOnly
  generatorDomUsesOnly :=
    pathUsesOnly_monotone isCovered atom.generatorDom atomUses.generatorDomUsesOnly
  generatorCodUsesOnly :=
    pathUsesOnly_monotone isCovered atom.generatorCod atomUses.generatorCodUsesOnly
  rightContextUsesOnly :=
    pathUsesOnly_monotone isCovered atom.rightContext atomUses.rightContextUsesOnly

/-- Growing the inventory preserves a trace's letter discipline. -/
theorem traceUsesOnly_monotone {signature : ModeSignature}
    {smallList bigList : List (PackedModality signature.graph)}
    (isCovered : ∀ edgeEntry, edgeEntry ∈ smallList → edgeEntry ∈ bigList)
    {sourceMode targetMode : signature.graph.Mode} :
    (trace : List (SpineAtom signature sourceMode targetMode)) →
    TraceUsesOnly smallList trace → TraceUsesOnly bigList trace
  | [], _traceUses => True.intro
  | _atom :: rest, traceUses =>
      ⟨atomUsesOnly_monotone isCovered traceUses.1,
        traceUsesOnly_monotone isCovered rest traceUses.2⟩

/-! ## Self-containment -/

/-- A path obeys its own letter list. -/
theorem pathUsesOnly_ownLetters {graph : ModeGraph} :
    {sourceMode targetMode : graph.Mode} →
    (path : ModalityPath graph sourceMode targetMode) →
    pathUsesOnly (pathLetters path) path
  | _, _, ModalityPath.nil _ => True.intro
  | _, _, ModalityPath.cons _edgeModality rest =>
      ⟨List.Mem.head (pathLetters rest),
        pathUsesOnly_monotone (fun _entry entryMem => List.Mem.tail _ entryMem) rest
          (pathUsesOnly_ownLetters rest)⟩

/-- An atom obeys its own letter block (each field maps into its block of the four-block
append). -/
theorem atomUsesOnly_ownLetters {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) :
    AtomUsesOnly (atomLetters atom) atom where
  leftContextUsesOnly :=
    pathUsesOnly_monotone
      (fun _entry entryMem => listMemAppendOfLeft _ entryMem)
      atom.leftContext (pathUsesOnly_ownLetters atom.leftContext)
  generatorDomUsesOnly :=
    pathUsesOnly_monotone
      (fun _entry entryMem =>
        listMemAppendOfRight _ (listMemAppendOfLeft _ entryMem))
      atom.generatorDom (pathUsesOnly_ownLetters atom.generatorDom)
  generatorCodUsesOnly :=
    pathUsesOnly_monotone
      (fun _entry entryMem =>
        listMemAppendOfRight _
          (listMemAppendOfRight _ (listMemAppendOfLeft _ entryMem)))
      atom.generatorCod (pathUsesOnly_ownLetters atom.generatorCod)
  rightContextUsesOnly :=
    pathUsesOnly_monotone
      (fun _entry entryMem =>
        listMemAppendOfRight _
          (listMemAppendOfRight _ (listMemAppendOfRight _ entryMem)))
      atom.rightContext (pathUsesOnly_ownLetters atom.rightContext)

/-- ★ **The seed obeys its own inventory**: head atom into its block, tail into the
rest. -/
theorem traceUsesOnly_ownInventory {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (trace : List (SpineAtom signature sourceMode targetMode)) →
    TraceUsesOnly (traceLetterInventory trace) trace
  | [] => True.intro
  | atom :: rest =>
      ⟨atomUsesOnly_monotone
          (fun _entry entryMem => listMemAppendOfLeft _ entryMem)
          (atomUsesOnly_ownLetters atom),
        traceUsesOnly_monotone
          (fun _entry entryMem => listMemAppendOfRight _ entryMem)
          rest (traceUsesOnly_ownInventory rest)⟩

/-! ## ★ The concrete universe-facing fact -/

/-- ★ **Every class-member atom uses only the seed's computable alphabet** — the letter
invariance instantiated at the seed's own inventory. -/
theorem memberAtomUsesOnly_seedInventory {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {seedTrace memberTrace : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv signature seedTrace memberTrace)
    {atom : SpineAtom signature overallSource overallTarget}
    (atomMem : atom ∈ memberTrace) :
    AtomUsesOnly (traceLetterInventory seedTrace) atom :=
  atomUsesOnly_ofSeed_ofTraceEquiv traceEquiv
    (traceUsesOnly_ownInventory seedTrace) atomMem

end FX1Poly.Polygraph
