import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCapEventPollution
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPairUntouched
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldSupport

/-! # ArcTouchConnectivity — the half-touch assembly's connectivity kit

The remaining small pieces the half-touch kill assembles over: the fold splits over a spine
decomposition, same-component facts read off as root equalities (giving symmetry and
transitivity for free at the root level), a cap's event connects to WHICHEVER read hits a
tracked node, a cap bumps the fresh counter by exactly one (the event-distinctness
arithmetic), and a probe connected to an unlinked node IS that node (the singleton-component
kill for the survival branch).

* `processArcSpine_append` — the fold over `front ++ back` is the fold over `back` from the
  mid-state (the split-certificate refolding);
* `unionFindRootOf_eq_ofSameComponent` / `isSameComponent_ofRootEq` — the two directions
  between the Bool component test and the root equality;
* `stepCapArc_nextFresh` — a cap allocates exactly one fresh node (its event);
* `isSameComponent_stepCapArc_eventSecondRead` / ★ `isSameComponent_stepCapArc_eventTouchedNode`
  — the cap's event reaches its second read through the consumed-pair join, hence reaches a
  tracked node hit by EITHER read;
* ★ `eq_ofSameComponent_ofUnlinked` — an unlinked node's component is a singleton
  (`nodesEqual_ofConnectedToUntouched` at the avoidance node-set), so a pinned connection to
  a survivor collapses to equality.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The fold splits over a spine decomposition -/

/-- The arc fold over an appended spine is the fold over the back half from the front half's
end state — the refolding that turns a split certificate's decomposition into a mid-state. -/
theorem processArcSpine_append {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (frontAtoms backAtoms : List (SpineAtom signature sourceMode targetMode)) →
    (state : ArcWireState) →
    processArcSpine state (frontAtoms ++ backAtoms)
      = processArcSpine (processArcSpine state frontAtoms) backAtoms
  | [], _, _ => rfl
  | atom :: rest, backAtoms, state => by
      show processArcSpine (stepArcAtom state atom) (rest ++ backAtoms)
        = processArcSpine (processArcSpine (stepArcAtom state atom) rest) backAtoms
      exact processArcSpine_append rest backAtoms (stepArcAtom state atom)

/-! ## Component tests as root equalities -/

/-- A positive component test IS a root equality — the reader direction. -/
theorem unionFindRootOf_eq_ofSameComponent (links : List (Nat × Nat))
    {firstNode secondNode : Nat}
    (connected : isSameComponent links firstNode secondNode = true) :
    unionFindRootOf links firstNode = unionFindRootOf links secondNode :=
  of_decide_eq_true connected

/-- A root equality IS a positive component test — the builder direction.  Together with the
reader this gives symmetry and transitivity of connectivity for free at the root level. -/
theorem isSameComponent_ofRootEq (links : List (Nat × Nat)) {firstNode secondNode : Nat}
    (rootsEq : unionFindRootOf links firstNode = unionFindRootOf links secondNode) :
    isSameComponent links firstNode secondNode = true := by
  show (unionFindRootOf links firstNode == unionFindRootOf links secondNode) = true
  rw [rootsEq]
  exact decide_eq_true rfl

/-! ## The cap's fresh allocation and its event's reach -/

/-- A cap allocates exactly one fresh node — its event.  The event-distinctness arithmetic
(a later event is strictly larger) reads the bump off this equation. -/
theorem stepCapArc_nextFresh (state : ArcWireState) (position : Nat) :
    (stepCapArc state position).nextFresh = state.nextFresh + 1 := rfl

/-- The cap's event also reaches its SECOND consumed read — through the first read and the
consumed-pair join, at the root level. -/
theorem isSameComponent_stepCapArc_eventSecondRead (state : ArcWireState) (position : Nat)
    (forest : isUnionFindForest state.links) :
    isSameComponent (stepCapArc state position).links
      state.nextFresh (natListGetAt state.openWires (position + 1)) = true :=
  isSameComponent_ofRootEq _
    (Eq.trans
      (unionFindRootOf_eq_ofSameComponent _
        (isSameComponent_stepCapArc_eventFirstRead state position forest))
      (unionFindRootOf_eq_ofSameComponent _
        (isSameComponent_stepCapArc_consumedReads state position forest)))

/-- ★ **The cap's event reaches a touched node**: whichever of the cap's two window reads
hits the tracked node, the fresh event lands in that node's component. -/
theorem isSameComponent_stepCapArc_eventTouchedNode (state : ArcWireState) (position : Nat)
    {node : Nat} (forest : isUnionFindForest state.links)
    (touched : natListGetAt state.openWires position = node
      ∨ natListGetAt state.openWires (position + 1) = node) :
    isSameComponent (stepCapArc state position).links state.nextFresh node = true := by
  cases touched with
  | inl firstReadHits =>
      rw [← firstReadHits]
      exact isSameComponent_stepCapArc_eventFirstRead state position forest
  | inr secondReadHits =>
      rw [← secondReadHits]
      exact isSameComponent_stepCapArc_eventSecondRead state position forest

/-! ## The singleton-component kill -/

/-- ★ **An unlinked node's component is a singleton**: any probe pinned into the same
component as a node that sits in NO edge must BE that node — the survival branch's
contradiction against the partner pin. -/
theorem eq_ofSameComponent_ofUnlinked (links : List (Nat × Nat))
    {probeNode unlinkedNode : Nat}
    (unlinked : ArcNodeUnlinked links unlinkedNode)
    (connected : isSameComponent links probeNode unlinkedNode = true) :
    probeNode = unlinkedNode :=
  nodesEqual_ofConnectedToUntouched (fun candidate => candidate ≠ unlinkedNode) links
    unlinked probeNode unlinkedNode (fun selfNe => selfNe rfl) connected

/-! ## Honesty marker -/

/-- **Honesty marker — the touch-connectivity kit is SHIPPED.**  The fold refolds over a
split decomposition, component tests convert to and from root equalities, a cap's fresh
event reaches whichever read touches a tracked node, the cap's fresh bump is exactly one,
and connection to an unlinked survivor collapses to equality.  NOT yet shipped: the
half-touch kill assembly itself (degenerate second scan + two distinct persisted events
against the cap-head count pin).  `= true`. -/
def fxMode_hasArcTouchConnectivityKit : Bool := true

end FX1Poly.Polygraph
