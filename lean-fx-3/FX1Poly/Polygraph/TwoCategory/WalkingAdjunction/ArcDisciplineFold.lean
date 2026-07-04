import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapDisciplinePreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision

/-! # ArcDisciplineFold — the typed-ends discipline holds along every chained adjunction fold

The campaign-C assembly: a boundary-chained walking-adjunction spine carries the
`ArcOpenEndsDiscipline` invariant through the whole arc fold.  Per atom, the chainedness
pins the fire window inside the boundary and the atom's arity picks the branch — a cup
fires at a `base`-parity window (`adjunctionCupAtom_windowPositionMode`) and preserves the
discipline by rung 2b, a cap fires at a `tip`-parity window
(`adjunctionCapAtom_windowPositionMode`) and preserves it by rung 2c — while freshness,
forestness, and the boundary tracking thread alongside through their existing per-step
lemmas.  At the canonical fresh seed everything holds vacuously, so every chained spine's
fold state is disciplined.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copy, following the codebase pattern) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-! ## Arity dispatch — one cup/cap arc step IS its branch -/

/-- A cup-arity atom's arc step IS the cup step at its window. -/
theorem stepArcAtom_eq_stepCupArc {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (hasCupDomArity : atom.generatorDom.length = 0)
    (hasCupCodArity : atom.generatorCod.length = 2) :
    stepArcAtom state atom = stepCupArc state atom.leftContext.length := by
  dsimp only [stepArcAtom]
  rw [hasCupDomArity, hasCupCodArity]

/-- A cap-arity atom's arc step IS the cap step at its window. -/
theorem stepArcAtom_eq_stepCapArc {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (hasCapDomArity : atom.generatorDom.length = 2)
    (hasCapCodArity : atom.generatorCod.length = 0) :
    stepArcAtom state atom = stepCapArc state atom.leftContext.length := by
  dsimp only [stepArcAtom]
  rw [hasCapDomArity, hasCapCodArity]

/-- One cup/cap arc step keeps the links a union-find forest. -/
theorem isUnionFindForest_stepArcAtom_ofCupOrCap {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (forest : isUnionFindForest state.links) :
    isUnionFindForest (stepArcAtom state atom).links := by
  cases arity with
  | inl cupArity =>
      rw [stepArcAtom_eq_stepCupArc state atom cupArity.1 cupArity.2]
      exact isUnionFindForest_stepCupArc state atom.leftContext.length forest
  | inr capArity =>
      rw [stepArcAtom_eq_stepCapArc state atom capArity.1 capArity.2]
      exact isUnionFindForest_stepCapArc state atom.leftContext.length forest

/-! ## The per-atom and whole-fold preservation at the walking adjunction -/

/-- ★ **One boundary-tracked adjunction atom preserves the typed-ends discipline.**  The
tracking premise bounds the fire window inside the boundary; the seed's arity disjunction
picks the branch; the window pins supply each branch's parity premise. -/
theorem arcOpenEndsDiscipline_stepArcAtom
    {overallSource overallTarget : adjunctionGraph.Mode}
    (state : ArcWireState)
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (discipline : ArcOpenEndsDiscipline overallSource state) :
    ArcOpenEndsDiscipline overallSource (stepArcAtom state atom) := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length :=
    tracksEntry
  cases adjunctionSpineAtom_hasCupOrCapArity atom with
  | inl cupArity =>
      obtain ⟨hasCupDomArity, hasCupCodArity⟩ := cupArity
      have positionInRange : atom.leftContext.length ≤ state.openWires.length := by
        rw [entryShape]
        exact Nat.le_trans
          (Nat.le_add_right atom.leftContext.length atom.generatorDom.length)
          (Nat.le_add_right (atom.leftContext.length + atom.generatorDom.length)
            atom.rightContext.length)
      rw [stepArcAtom_eq_stepCupArc state atom hasCupDomArity hasCupCodArity]
      exact arcOpenEndsDiscipline_stepCupArc overallSource state atom.leftContext.length
        fresh forest positionInRange
        (adjunctionCupAtom_windowPositionMode atom hasCupDomArity) discipline
  | inr capArity =>
      obtain ⟨hasCapDomArity, hasCapCodArity⟩ := capArity
      have windowInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, hasCapDomArity]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepArcAtom_eq_stepCapArc state atom hasCapDomArity hasCapCodArity]
      exact arcOpenEndsDiscipline_stepCapArc overallSource state atom.leftContext.length
        fresh forest windowInRange
        (adjunctionCapAtom_windowPositionMode atom hasCapDomArity) discipline

/-- ★ **A chained adjunction spine carries the typed-ends discipline through the whole arc
fold** — freshness, forestness, and boundary tracking thread alongside through their
per-step lemmas, and each atom's step preserves the discipline. -/
theorem arcOpenEndsDiscipline_processArcSpine
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength : Nat) →
    ArcStateFresh state → isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    ArcOpenEndsDiscipline overallSource state →
    ArcOpenEndsDiscipline overallSource (processArcSpine state atoms)
  | [], _, _, _, _, _, _, discipline => discipline
  | headAtom :: restAtoms, state, _, fresh, forest, tracks, chained, discipline => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have headArity := adjunctionSpineAtom_hasCupOrCapArity headAtom
      show ArcOpenEndsDiscipline overallSource
        (processArcSpine (stepArcAtom state headAtom) restAtoms)
      exact arcOpenEndsDiscipline_processArcSpine restAtoms (stepArcAtom state headAtom)
        headAtom.codBoundaryLength
        (arcStateFresh_stepArcAtom state headAtom fresh)
        (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom headArity forest)
        (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained
        (arcOpenEndsDiscipline_stepArcAtom state headAtom fresh forest tracksEntry
          discipline)

/-- ★ **The capstone at the canonical seed**: every boundary-chained walking-adjunction
spine folds from the fresh initial state into a DISCIPLINED arc state — the state whose
`extractArc` reading `arcStructureOfSpineList` takes. -/
theorem arcOpenEndsDiscipline_ofChainedSpineList
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms) :
    ArcOpenEndsDiscipline overallSource
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms) :=
  arcOpenEndsDiscipline_processArcSpine atoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount
    (arcStateFresh_initial bottomCount) isUnionFindForest_nil (rangeLength bottomCount)
    chained (arcOpenEndsDiscipline_initial overallSource bottomCount)

/-! ## Honesty marker -/

/-- **Honesty marker — the typed-ends discipline FOLD is SHIPPED (peel campaign C, fold
assembly).**  Arity dispatch equations (`stepArcAtom_eq_stepCupArc`/`_eq_stepCapArc`), the
cup/cap forest step, the per-atom preservation at the walking adjunction
(`arcOpenEndsDiscipline_stepArcAtom` — chainedness gives the window bound, the seed pins
give the parity), the whole-spine fold (`arcOpenEndsDiscipline_processArcSpine`), and the
canonical-seed capstone (`arcOpenEndsDiscipline_ofChainedSpineList`).  What this marker
does NOT claim: the loop-freedom consequence (rung 3 — the same-component cap refutation
turning `loops = 0` along chained folds) and the leg-separation payoff the peel's H
campaign consumes.  `= true`. -/
def fxMode_hasArcDisciplineFold : Bool := true

end FX1Poly.Polygraph
