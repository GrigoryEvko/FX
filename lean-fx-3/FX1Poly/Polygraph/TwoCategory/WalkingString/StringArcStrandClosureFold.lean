import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStrandClosureFold
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcArity

/-! # WalkingString/StringArcStrandClosureFold — a closed strand stays closed through the fold, ported
(FC-3 r19, THE CAP-HEAD DISCHARGE PORT — LOCATE/count substrate)

Phantom-signature two-token clone of the walking-adjunction `ArcStrandClosureFold`'s spine-level set, re-plumbed
onto the FOUR-generator seed.  The per-step invariant preservations (`arcStrandClosure_stepCupArc`/`stepCapArc`) and
the query-stability step lemmas are `{signature}`-generic and REUSED by import; only the per-atom dispatch and the
two whole-spine folds quantify over `SpineAtom` and so clone (their only non-generic dependency is the seed
classification `adjointTripleSpineAtom_hasCupOrCapArity`).

  * `stringIsSameComponent_stepArcAtom_queriesStable` / `stringArcStrandClosure_stepArcAtom` — the per-atom dispatch;
  * ★ `stringArcStrandClosure_processArcSpine` / `stringIsSameComponent_processArcSpine_queriesStable` — the folds.

Raw Lean 4 + Init; structural recursion only; no `omega` / `simp`-AC / `WellFounded.fix`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Per-atom dispatch at the walking adjoint triple -/

/-- **One boundary-tracked atom changes no query against a closed anchor** (four-generator port). -/
theorem stringIsSameComponent_stepArcAtom_queriesStable
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (state : ArcWireState)
    (atom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (forest : isUnionFindForest state.links) (anchorNode : Nat)
    (closure : ArcStrandClosure anchorNode state) (probeNode : Nat) :
    isSameComponent (stepArcAtom state atom).links anchorNode probeNode
      = isSameComponent state.links anchorNode probeNode := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length :=
    tracksEntry
  cases adjointTripleSpineAtom_hasCupOrCapArity atom with
  | inl cupArity =>
      rw [stepArcAtom_eq_stepCupArc state atom cupArity.1 cupArity.2]
      exact isSameComponent_stepCupArc_queriesStable state atom.leftContext.length forest
        anchorNode closure.missesFreshNodes probeNode
  | inr capArity =>
      have windowInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, capArity.1]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      have positionBelowLength : atom.leftContext.length < state.openWires.length :=
        Nat.lt_of_lt_of_le
          (Nat.lt_trans (Nat.lt_succ_self atom.leftContext.length)
            (Nat.lt_succ_self (atom.leftContext.length + 1)))
          windowInRange
      have succBelowLength : atom.leftContext.length + 1 < state.openWires.length :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self (atom.leftContext.length + 1)) windowInRange
      rw [stepArcAtom_eq_stepCapArc state atom capArity.1 capArity.2]
      exact isSameComponent_stepCapArc_queriesStable state atom.leftContext.length forest
        anchorNode
        (closure.missesOpenWires atom.leftContext.length positionBelowLength)
        (closure.missesOpenWires (atom.leftContext.length + 1) succBelowLength)
        closure.missesFreshNodes probeNode

/-- **One boundary-tracked atom preserves the closed-strand invariant** (four-generator port). -/
theorem stringArcStrandClosure_stepArcAtom
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (state : ArcWireState)
    (atom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (forest : isUnionFindForest state.links) (anchorNode : Nat)
    (closure : ArcStrandClosure anchorNode state) :
    ArcStrandClosure anchorNode (stepArcAtom state atom) := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length :=
    tracksEntry
  cases adjointTripleSpineAtom_hasCupOrCapArity atom with
  | inl cupArity =>
      have positionInRange : atom.leftContext.length ≤ state.openWires.length := by
        rw [entryShape]
        exact Nat.le_trans
          (Nat.le_add_right atom.leftContext.length atom.generatorDom.length)
          (Nat.le_add_right (atom.leftContext.length + atom.generatorDom.length)
            atom.rightContext.length)
      rw [stepArcAtom_eq_stepCupArc state atom cupArity.1 cupArity.2]
      exact arcStrandClosure_stepCupArc state atom.leftContext.length forest anchorNode
        positionInRange closure
  | inr capArity =>
      have windowInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, capArity.1]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepArcAtom_eq_stepCapArc state atom capArity.1 capArity.2]
      exact arcStrandClosure_stepCapArc state atom.leftContext.length forest anchorNode
        windowInRange closure

/-! ## The whole-spine folds -/

/-- ★ **A chained string spine's arc fold preserves the closed-strand invariant end-to-end** (four-generator port). -/
theorem stringArcStrandClosure_processArcSpine
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength : Nat) →
    isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    (anchorNode : Nat) → ArcStrandClosure anchorNode state →
    ArcStrandClosure anchorNode (processArcSpine state atoms)
  | [], _, _, _, _, _, _, closure => closure
  | headAtom :: restAtoms, state, _, forest, tracks, chained, anchorNode, closure => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have headArity := adjointTripleSpineAtom_hasCupOrCapArity headAtom
      show ArcStrandClosure anchorNode
        (processArcSpine (stepArcAtom state headAtom) restAtoms)
      exact stringArcStrandClosure_processArcSpine restAtoms (stepArcAtom state headAtom)
        headAtom.codBoundaryLength
        (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom headArity forest)
        (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained anchorNode
        (stringArcStrandClosure_stepArcAtom state headAtom tracksEntry forest anchorNode
          closure)

/-- ★ **A chained string spine's arc fold changes no query against a closed anchor** (four-generator port). -/
theorem stringIsSameComponent_processArcSpine_queriesStable
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength : Nat) →
    isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    (anchorNode : Nat) → ArcStrandClosure anchorNode state →
    (probeNode : Nat) →
    isSameComponent (processArcSpine state atoms).links anchorNode probeNode
      = isSameComponent state.links anchorNode probeNode
  | [], _, _, _, _, _, _, _, _ => rfl
  | headAtom :: restAtoms, state, _, forest, tracks, chained, anchorNode, closure,
      probeNode => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have headArity := adjointTripleSpineAtom_hasCupOrCapArity headAtom
      show isSameComponent
          (processArcSpine (stepArcAtom state headAtom) restAtoms).links anchorNode
          probeNode
        = isSameComponent state.links anchorNode probeNode
      exact (stringIsSameComponent_processArcSpine_queriesStable restAtoms
          (stepArcAtom state headAtom) headAtom.codBoundaryLength
          (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom headArity forest)
          (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
          tailChained anchorNode
          (stringArcStrandClosure_stepArcAtom state headAtom tracksEntry forest anchorNode
            closure)
          probeNode).trans
        (stringIsSameComponent_stepArcAtom_queriesStable state headAtom tracksEntry forest
          anchorNode closure probeNode)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the closed-strand fold ported to the adjoint-triple seed (FC-3 r19).**  The per-atom dispatch
and the two whole-spine folds (`stringArcStrandClosure_processArcSpine`,
`stringIsSameComponent_processArcSpine_queriesStable`) — phantom-signature two-token clones of `ArcStrandClosureFold`,
riding `adjointTripleSpineAtom_hasCupOrCapArity` and the `{signature}`-generic per-step preservations (reused, never
cloned).  Feeds the cap-head seed-closure instantiation.  `= true`. -/
def fxString_hasArcStrandClosureFold : Bool := true

end FX1Poly.Polygraph
