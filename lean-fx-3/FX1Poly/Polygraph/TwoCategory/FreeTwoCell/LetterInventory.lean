import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # LetterInventory — context letters stay inside a fixed edge inventory (FREE-7)

Second invariance brick of the BOUNDED-ATOM-UNIVERSE route: a swap builds its new
whisker contexts by RECOMBINING factors of the old ones with the (riding) generators'
boundary 1-cells — no new modality letter can ever appear.  So "every letter of every
atom lies in the edge list `E`" is a class invariant, giving the atom universe its
letter dimension: reachable contexts are paths over a FIXED finite letter alphabet.

  * `PackedModality` — a graph edge packaged with its endpoint modes (the inventory
    entry for a 1-cell letter);
  * `pathUsesOnly` — every letter of a path is in the inventory (cons-only Prop);
  * `pathUsesOnly_composePath_split` / `_join` — the factor kit: letters of a composite
    are exactly the letters of its factors;
  * `AtomUsesOnly` / `TraceUsesOnly` — the per-atom (contexts AND generator boundaries)
    and per-trace disciplines;
  * ★ `AtomicTraceEquiv.usesOnlyIff` — the letter discipline is invariant across the
    whole trace equivalence (the swap case splits the old contexts into their factors
    and rejoins them into the new ones);
  * `atomUsesOnly_ofSeed_ofTraceEquiv` — the universe-facing corollary: every atom of a
    class member draws its letters from any inventory covering the seed.

Downstream: with the generator inventory (`GeneratorInventory.lean`) pinning WHICH
generators occur and the width budget pinning HOW LONG contexts can be, this brick pins
WHAT the contexts are made of — the three finiteness legs of the atom universe `U`.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The letter inventory entry + the path discipline -/

/-- A 1-cell letter packaged with its endpoint modes — the inventory entry. -/
structure PackedModality (graph : ModeGraph) where
  /-- The letter's source mode. -/
  edgeSourceMode : graph.Mode
  /-- The letter's target mode. -/
  edgeTargetMode : graph.Mode
  /-- The letter itself. -/
  edgeModality : graph.Modality edgeSourceMode edgeTargetMode

/-- Every letter of the path is in the inventory (cons-only recursion). -/
def pathUsesOnly {graph : ModeGraph} (edgeList : List (PackedModality graph)) :
    {sourceMode targetMode : graph.Mode} →
    ModalityPath graph sourceMode targetMode → Prop
  | _, _, ModalityPath.nil _ => True
  | _, _, ModalityPath.cons edgeModality rest =>
      (⟨_, _, edgeModality⟩ : PackedModality graph) ∈ edgeList
        ∧ pathUsesOnly edgeList rest

/-- Splitting the factor kit: a composite's letter discipline yields both factors'. -/
theorem pathUsesOnly_composePath_split {graph : ModeGraph}
    (edgeList : List (PackedModality graph)) :
    {sourceMode middleMode targetMode : graph.Mode} →
    (firstPath : ModalityPath graph sourceMode middleMode) →
    (secondPath : ModalityPath graph middleMode targetMode) →
    pathUsesOnly edgeList (composePath firstPath secondPath) →
    pathUsesOnly edgeList firstPath ∧ pathUsesOnly edgeList secondPath
  | _, _, _, ModalityPath.nil _, _secondPath, compositeUses =>
      ⟨True.intro, compositeUses⟩
  | _, _, _, ModalityPath.cons _edgeModality rest, secondPath, compositeUses => by
      obtain ⟨edgeMem, restCompositeUses⟩ := compositeUses
      obtain ⟨restUses, secondUses⟩ :=
        pathUsesOnly_composePath_split edgeList rest secondPath restCompositeUses
      exact ⟨⟨edgeMem, restUses⟩, secondUses⟩

/-- Joining the factor kit: both factors' letter disciplines yield the composite's. -/
theorem pathUsesOnly_composePath_join {graph : ModeGraph}
    (edgeList : List (PackedModality graph)) :
    {sourceMode middleMode targetMode : graph.Mode} →
    (firstPath : ModalityPath graph sourceMode middleMode) →
    (secondPath : ModalityPath graph middleMode targetMode) →
    pathUsesOnly edgeList firstPath → pathUsesOnly edgeList secondPath →
    pathUsesOnly edgeList (composePath firstPath secondPath)
  | _, _, _, ModalityPath.nil _, _secondPath, _firstUses, secondUses => secondUses
  | _, _, _, ModalityPath.cons _edgeModality rest, secondPath, firstUses, secondUses => by
      obtain ⟨edgeMem, restUses⟩ := firstUses
      exact ⟨edgeMem,
        pathUsesOnly_composePath_join edgeList rest secondPath restUses secondUses⟩

/-! ## The atom and trace disciplines -/

/-- Every letter of the atom — whisker contexts AND generator boundaries — is in the
inventory. -/
structure AtomUsesOnly {signature : ModeSignature}
    (edgeList : List (PackedModality signature.graph))
    {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) : Prop where
  /-- The left whisker context's letters. -/
  leftContextUsesOnly : pathUsesOnly edgeList atom.leftContext
  /-- The generator's source boundary letters. -/
  generatorDomUsesOnly : pathUsesOnly edgeList atom.generatorDom
  /-- The generator's target boundary letters. -/
  generatorCodUsesOnly : pathUsesOnly edgeList atom.generatorCod
  /-- The right whisker context's letters. -/
  rightContextUsesOnly : pathUsesOnly edgeList atom.rightContext

/-- Every atom of the trace obeys the letter discipline (cons-only recursion). -/
def TraceUsesOnly {signature : ModeSignature}
    (edgeList : List (PackedModality signature.graph))
    {sourceMode targetMode : signature.graph.Mode} :
    List (SpineAtom signature sourceMode targetMode) → Prop
  | [] => True
  | atom :: rest => AtomUsesOnly edgeList atom ∧ TraceUsesOnly edgeList rest

/-- Project the discipline onto a member atom. -/
theorem traceUsesOnly_projectAtom {signature : ModeSignature}
    {edgeList : List (PackedModality signature.graph)}
    {sourceMode targetMode : signature.graph.Mode}
    {trace : List (SpineAtom signature sourceMode targetMode)}
    (traceUses : TraceUsesOnly edgeList trace)
    {atom : SpineAtom signature sourceMode targetMode} (atomMem : atom ∈ trace) :
    AtomUsesOnly edgeList atom := by
  induction atomMem with
  | head _ => exact traceUses.1
  | tail _ _innerMem innerHypothesis => exact innerHypothesis traceUses.2

/-! ## ★ The letter invariance -/

/-- ★ **The letter discipline is a class invariant**: a swap recombines factors of the
old contexts with the riding generators' boundaries — splitting the old composites and
rejoining the pieces covers both new atoms, in both directions. -/
theorem AtomicTraceEquiv.usesOnlyIff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv signature firstList secondList)
    (edgeList : List (PackedModality signature.graph)) :
    TraceUsesOnly edgeList firstList ↔ TraceUsesOnly edgeList secondList := by
  induction traceEquiv with
  | ofSwap swapStep =>
      cases swapStep with
      | @swap _swapSourceMode _swapMiddleLeft _swapMiddleRight _swapTargetMode oneCellFMid
          oneCellFHigh oneCellGLow oneCellGMid generatorLeft generatorRight leftAcc
          inertPath rightAcc rest =>
          constructor
          · intro allUses
            obtain ⟨leftAtomUses, rightAtomUses, restUses⟩ := allUses
            obtain ⟨inertGLowUses, rightAccUses⟩ :=
              pathUsesOnly_composePath_split edgeList
                (composePath inertPath oneCellGLow) rightAcc
                leftAtomUses.rightContextUsesOnly
            obtain ⟨inertUses, _gLowUses⟩ :=
              pathUsesOnly_composePath_split edgeList inertPath oneCellGLow inertGLowUses
            refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, restUses⟩
            · exact pathUsesOnly_composePath_join edgeList
                (composePath leftAcc oneCellFMid) inertPath
                (pathUsesOnly_composePath_join edgeList leftAcc oneCellFMid
                  leftAtomUses.leftContextUsesOnly leftAtomUses.generatorDomUsesOnly)
                inertUses
            · exact rightAtomUses.generatorDomUsesOnly
            · exact rightAtomUses.generatorCodUsesOnly
            · exact rightAtomUses.rightContextUsesOnly
            · exact leftAtomUses.leftContextUsesOnly
            · exact leftAtomUses.generatorDomUsesOnly
            · exact leftAtomUses.generatorCodUsesOnly
            · exact pathUsesOnly_composePath_join edgeList
                (composePath inertPath oneCellGMid) rightAcc
                (pathUsesOnly_composePath_join edgeList inertPath oneCellGMid
                  inertUses rightAtomUses.generatorCodUsesOnly)
                rightAccUses
          · intro allUses
            obtain ⟨movedLeftAtomUses, movedRightAtomUses, restUses⟩ := allUses
            obtain ⟨leftAccFMidUses, inertUses⟩ :=
              pathUsesOnly_composePath_split edgeList
                (composePath leftAcc oneCellFMid) inertPath
                movedLeftAtomUses.leftContextUsesOnly
            obtain ⟨leftAccUses, _fMidUses⟩ :=
              pathUsesOnly_composePath_split edgeList leftAcc oneCellFMid leftAccFMidUses
            obtain ⟨_inertGMidUses, rightAccUses⟩ :=
              pathUsesOnly_composePath_split edgeList
                (composePath inertPath oneCellGMid) rightAcc
                movedRightAtomUses.rightContextUsesOnly
            refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, restUses⟩
            · exact movedRightAtomUses.leftContextUsesOnly
            · exact movedRightAtomUses.generatorDomUsesOnly
            · exact movedRightAtomUses.generatorCodUsesOnly
            · exact pathUsesOnly_composePath_join edgeList
                (composePath inertPath oneCellGLow) rightAcc
                (pathUsesOnly_composePath_join edgeList inertPath oneCellGLow
                  inertUses movedLeftAtomUses.generatorDomUsesOnly)
                rightAccUses
            · exact pathUsesOnly_composePath_join edgeList
                (composePath leftAcc oneCellFHigh) inertPath
                (pathUsesOnly_composePath_join edgeList leftAcc oneCellFHigh
                  leftAccUses movedRightAtomUses.generatorCodUsesOnly)
                inertUses
            · exact movedLeftAtomUses.generatorDomUsesOnly
            · exact movedLeftAtomUses.generatorCodUsesOnly
            · exact movedLeftAtomUses.rightContextUsesOnly
  | refl _ => exact Iff.rfl
  | symm _ innerHypothesis => exact innerHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis
  | consCongr atom _ innerHypothesis =>
      exact ⟨fun ⟨headUses, restUses⟩ => ⟨headUses, innerHypothesis.mp restUses⟩,
        fun ⟨headUses, restUses⟩ => ⟨headUses, innerHypothesis.mpr restUses⟩⟩

/-- The universe-facing corollary: every atom of a class member draws its letters from
any inventory covering the seed. -/
theorem atomUsesOnly_ofSeed_ofTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {seedTrace memberTrace : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv signature seedTrace memberTrace)
    {edgeList : List (PackedModality signature.graph)}
    (seedUses : TraceUsesOnly edgeList seedTrace)
    {atom : SpineAtom signature overallSource overallTarget}
    (atomMem : atom ∈ memberTrace) :
    AtomUsesOnly edgeList atom :=
  traceUsesOnly_projectAtom ((traceEquiv.usesOnlyIff edgeList).mp seedUses) atomMem

end FX1Poly.Polygraph
