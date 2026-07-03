import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentSim
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # mode-3 keystone — the join-event trace of the matching fold (reification + faithfulness)

The sigma witness's remaining fields (`componentComm`, `loopsEq`) compare the PARTITIONS the two
transposed Godement orders build.  Neither order's intermediate states correspond under the rotation
(each order's second block starts on a partition the other order has not built yet), so the comparison
must go through VIRTUAL join sequences no run realizes — which requires reifying each run's partition
action as DATA.  This file ships that reification:

  * `stepAtomJoinEvents` / `spineJoinEvents` — the join-event trace: a cup emits its two fresh legs, a
    cap emits its two read wires, a box emits nothing.  The trace depends only on the WIRE evolution
    (positions and counters), which the shipped window congruences already relate across the orders.
  * `applyJoinEvents` + ★ faithfulness (`processSpine_links_eq_applyJoinEvents`): the fold's `links`
    output IS the homogeneous join fold over the trace — UNCONDITIONALLY, because the cup's update is a
    literal join and the cap's outer test is redundant for links (`stepCap_links_eq_unionFindJoin`).
  * `countJoinEventLoops` + ★ faithfulness (`processSpine_loops_eq_addJoinEventLoops`): the fold's loop
    increment IS the count of already-connected event pairs at fold time — conditioned on link
    freshness, because a cup's fresh legs must test disconnected
    (`isSameComponent_freshPair_eq_false`, via the out-of-support root identity
    `unionFindRootOf_eq_self_ofFresh`).
  * ★ `componentView_applyJoinEvents` / `countJoinEventLoops_map_congr` — the sigma-equivariance of the
    event fold: pointwise-renamed event lists carry a same-component correspondence and preserve the
    loop count (iterating `componentView_unionFindJoin`).  With these, the block-swap `componentComm` /
    `loopsEq` reduce to the pure EXCHANGE of the two blocks' event lists at fixed ids — the next brick.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Out-of-support roots (the fresh-pair test) -/

private theorem natSelfNeSucc : (value : Nat) → value = value + 1 → False
  | 0, selfEqSucc => Nat.noConfusion selfEqSucc
  | value + 1, selfEqSucc => natSelfNeSucc value (Nat.succ.inj selfEqSucc)

/-- A node at or above every recorded child has no parent entry. -/
theorem unionFindParent_eq_none_ofFresh (bound : Nat) :
    (links : List (Nat × Nat)) → (∀ edge ∈ links, edge.1 < bound) →
    (node : Nat) → bound ≤ node →
    unionFindParent links node = none
  | [], _, _, _ => rfl
  | (child, parent) :: rest, boundedChildren, node, nodeAtLeast => by
      show (if child == node then some parent else unionFindParent rest node) = none
      rw [show (child == node) = false from decide_eq_false (fun childEqNode =>
        Nat.lt_irrefl node (Nat.lt_of_lt_of_le
          (childEqNode ▸ boundedChildren (child, parent) (List.Mem.head rest)) nodeAtLeast))]
      exact unionFindParent_eq_none_ofFresh bound rest
        (fun edge edgeInRest => boundedChildren edge (List.Mem.tail (child, parent) edgeInRest))
        node nodeAtLeast

private theorem unionFindRoot_eq_self_ofParentNone :
    (fuel : Nat) → (links : List (Nat × Nat)) → (node : Nat) →
    unionFindParent links node = none →
    unionFindRoot fuel links node = node
  | 0, _, _, _ => rfl
  | fuel + 1, links, node, parentNone => by
      have oneStep : unionFindRoot (fuel + 1) links node
          = match unionFindParent links node with
            | none => node
            | some parent => unionFindRoot fuel links parent := rfl
      rw [oneStep, parentNone]

/-- **A fresh node is its own root** — an id at or above every recorded child is outside the union-find's
support, so the parent chase stops immediately. -/
theorem unionFindRootOf_eq_self_ofFresh (bound : Nat) (links : List (Nat × Nat))
    (boundedChildren : ∀ edge ∈ links, edge.1 < bound) (node : Nat) (nodeAtLeast : bound ≤ node) :
    unionFindRootOf links node = node :=
  unionFindRoot_eq_self_ofParentNone (links.length + 1) links node
    (unionFindParent_eq_none_ofFresh bound links boundedChildren node nodeAtLeast)

/-- **A cup's two fresh legs are never already connected** — both are their own roots (out of support)
and they differ. -/
theorem isSameComponent_freshPair_eq_false (bound : Nat) (links : List (Nat × Nat))
    (boundedChildren : ∀ edge ∈ links, edge.1 < bound) (node : Nat) (nodeAtLeast : bound ≤ node) :
    isSameComponent links node (node + 1) = false := by
  show (unionFindRootOf links node == unionFindRootOf links (node + 1)) = false
  rw [unionFindRootOf_eq_self_ofFresh bound links boundedChildren node nodeAtLeast,
    unionFindRootOf_eq_self_ofFresh bound links boundedChildren (node + 1)
      (Nat.le_succ_of_le nodeAtLeast)]
  exact decide_eq_false (natSelfNeSucc node)

/-! ## The join-event trace -/

/-- The join events one atom fires: a cup emits its two fresh legs, a cap emits its two read wires, a
box emits nothing (its links are untouched).  Mirrors `stepAtom`'s arity match so the two matchers
reduce together under literal arities. -/
def stepAtomJoinEvents {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode) : List (Nat × Nat) :=
  match atom.generatorDom.length, atom.generatorCod.length with
  | 0, 2 => [(state.nextFresh, state.nextFresh + 1)]
  | 2, 0 => [(natListGetAt state.openWires atom.leftContext.length,
      natListGetAt state.openWires (atom.leftContext.length + 1))]
  | _, _ => []

/-- Fold a list of join events over a link list — the homogeneous partition action of a trace. -/
def applyJoinEvents : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], links => links
  | (firstNode, secondNode) :: restEvents, links =>
      applyJoinEvents restEvents (unionFindJoin links firstNode secondNode)

/-- Count the events whose pair is ALREADY connected at fold time — the loop increments of a trace. -/
def countJoinEventLoops : List (Nat × Nat) → List (Nat × Nat) → Nat
  | [], _ => 0
  | (firstNode, secondNode) :: restEvents, links =>
      (isSameComponent links firstNode secondNode).toNat
        + countJoinEventLoops restEvents (unionFindJoin links firstNode secondNode)

/-- The join-event trace of a whole spine, threading the wire state (events read positions and
counters, so the trace is a function of the WIRE evolution alone). -/
def spineJoinEvents {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    List (SpineAtom signature sourceMode targetMode) → WireState → List (Nat × Nat)
  | [], _ => []
  | atom :: restAtoms, state =>
      stepAtomJoinEvents state atom ++ spineJoinEvents restAtoms (stepAtom state atom)

/-- A `0 ⇒ 2` generator's trace is its two fresh legs. -/
theorem stepAtomJoinEvents_ofCupArity {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (hdom : atom.generatorDom.length = 0) (hcod : atom.generatorCod.length = 2) :
    stepAtomJoinEvents state atom = [(state.nextFresh, state.nextFresh + 1)] := by
  unfold stepAtomJoinEvents
  rw [hdom, hcod]

/-- A `2 ⇒ 0` generator's trace is its two read wires. -/
theorem stepAtomJoinEvents_ofCapArity {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (hdom : atom.generatorDom.length = 2) (hcod : atom.generatorCod.length = 0) :
    stepAtomJoinEvents state atom
      = [(natListGetAt state.openWires atom.leftContext.length,
          natListGetAt state.openWires (atom.leftContext.length + 1))] := by
  unfold stepAtomJoinEvents
  rw [hdom, hcod]

/-! ## Trace composition -/

/-- The event fold splits over concatenation. -/
theorem applyJoinEvents_append :
    (firstEvents secondEvents : List (Nat × Nat)) → (links : List (Nat × Nat)) →
    applyJoinEvents (firstEvents ++ secondEvents) links
      = applyJoinEvents secondEvents (applyJoinEvents firstEvents links)
  | [], _, _ => rfl
  | (firstNode, secondNode) :: restEvents, secondEvents, links =>
      applyJoinEvents_append restEvents secondEvents (unionFindJoin links firstNode secondNode)

/-- The loop count splits over concatenation (the tail counted on the head's output links). -/
theorem countJoinEventLoops_append :
    (firstEvents secondEvents : List (Nat × Nat)) → (links : List (Nat × Nat)) →
    countJoinEventLoops (firstEvents ++ secondEvents) links
      = countJoinEventLoops firstEvents links
        + countJoinEventLoops secondEvents (applyJoinEvents firstEvents links)
  | [], _, _ => (Nat.zero_add _).symm
  | (firstNode, secondNode) :: restEvents, secondEvents, links => by
      show (isSameComponent links firstNode secondNode).toNat
            + countJoinEventLoops (restEvents ++ secondEvents)
                (unionFindJoin links firstNode secondNode)
          = (isSameComponent links firstNode secondNode).toNat
              + countJoinEventLoops restEvents (unionFindJoin links firstNode secondNode)
              + countJoinEventLoops secondEvents
                  (applyJoinEvents restEvents (unionFindJoin links firstNode secondNode))
      rw [countJoinEventLoops_append restEvents secondEvents
          (unionFindJoin links firstNode secondNode),
        Nat.add_assoc]

/-! ## Faithfulness: the fold's links ARE the event fold -/

/-- ★ **One atom's link update is exactly its trace's join fold** — UNCONDITIONALLY.  The cup's update
is a literal join of the fresh legs, the cap's is a join of its read pair
(`stepCap_links_eq_unionFindJoin` — the outer test is redundant for links), the box touches nothing.
Literal-arity case tree so both matchers reduce. -/
theorem stepAtom_links_eq_applyJoinEvents {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode) :
    (stepAtom state atom).links = applyJoinEvents (stepAtomJoinEvents state atom) state.links := by
  cases hdom : atom.generatorDom.length with
  | zero =>
      cases hcod : atom.generatorCod.length with
      | zero => unfold stepAtom stepAtomJoinEvents; rw [hdom, hcod]; rfl
      | succ codPred =>
          cases codPred with
          | zero => unfold stepAtom stepAtomJoinEvents; rw [hdom, hcod]; rfl
          | succ codPredPred =>
              cases codPredPred with
              | zero =>
                  rw [stepAtom_ofCupArity state atom hdom hcod,
                    stepAtomJoinEvents_ofCupArity state atom hdom hcod]
                  rfl
              | succ _ => unfold stepAtom stepAtomJoinEvents; rw [hdom, hcod]; rfl
  | succ domPred =>
      cases domPred with
      | zero => unfold stepAtom stepAtomJoinEvents; rw [hdom]; rfl
      | succ domPredPred =>
          cases domPredPred with
          | zero =>
              cases hcod : atom.generatorCod.length with
              | zero =>
                  rw [stepAtom_ofCapArity state atom hdom hcod,
                    stepAtomJoinEvents_ofCapArity state atom hdom hcod,
                    stepCap_links_eq_unionFindJoin state atom.leftContext.length]
                  rfl
              | succ _ => unfold stepAtom stepAtomJoinEvents; rw [hdom, hcod]; rfl
          | succ _ => unfold stepAtom stepAtomJoinEvents; rw [hdom]; rfl

/-- ★ **One atom's loop increment is exactly its trace's already-connected count** — conditioned on
link freshness (children below the counter), so the cup's fresh pair tests disconnected.  The cap's
increment is its outer test (`stepCap_loops_eq_addIncrement`), the box adds nothing. -/
theorem stepAtom_loops_eq_addJoinEventLoops {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (linksBounded : ∀ edge ∈ state.links, edge.1 < state.nextFresh) :
    (stepAtom state atom).loops
      = state.loops + countJoinEventLoops (stepAtomJoinEvents state atom) state.links := by
  cases hdom : atom.generatorDom.length with
  | zero =>
      cases hcod : atom.generatorCod.length with
      | zero => unfold stepAtom stepAtomJoinEvents; rw [hdom, hcod]; rfl
      | succ codPred =>
          cases codPred with
          | zero => unfold stepAtom stepAtomJoinEvents; rw [hdom, hcod]; rfl
          | succ codPredPred =>
              cases codPredPred with
              | zero =>
                  rw [stepAtom_ofCupArity state atom hdom hcod,
                    stepAtomJoinEvents_ofCupArity state atom hdom hcod]
                  show state.loops
                      = state.loops
                        + ((isSameComponent state.links state.nextFresh
                              (state.nextFresh + 1)).toNat
                            + countJoinEventLoops []
                                (unionFindJoin state.links state.nextFresh
                                  (state.nextFresh + 1)))
                  rw [isSameComponent_freshPair_eq_false state.nextFresh state.links
                    linksBounded state.nextFresh (Nat.le_refl state.nextFresh)]
                  rfl
              | succ _ => unfold stepAtom stepAtomJoinEvents; rw [hdom, hcod]; rfl
  | succ domPred =>
      cases domPred with
      | zero => unfold stepAtom stepAtomJoinEvents; rw [hdom]; rfl
      | succ domPredPred =>
          cases domPredPred with
          | zero =>
              cases hcod : atom.generatorCod.length with
              | zero =>
                  rw [stepAtom_ofCapArity state atom hdom hcod,
                    stepAtomJoinEvents_ofCapArity state atom hdom hcod,
                    stepCap_loops_eq_addIncrement state atom.leftContext.length]
                  rfl
              | succ _ => unfold stepAtom stepAtomJoinEvents; rw [hdom, hcod]; rfl
          | succ _ => unfold stepAtom stepAtomJoinEvents; rw [hdom]; rfl

/-! ## Faithfulness at spine and cell granularity -/

/-- ★ **The whole fold's links are the event fold of its trace** — unconditionally. -/
theorem processSpine_links_eq_applyJoinEvents {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : WireState) →
    (processSpine state atoms).links
      = applyJoinEvents (spineJoinEvents atoms state) state.links
  | [], _ => rfl
  | atom :: restAtoms, state => by
      show (processSpine (stepAtom state atom) restAtoms).links
          = applyJoinEvents
              (stepAtomJoinEvents state atom
                ++ spineJoinEvents restAtoms (stepAtom state atom))
              state.links
      rw [processSpine_links_eq_applyJoinEvents restAtoms (stepAtom state atom),
        stepAtom_links_eq_applyJoinEvents state atom,
        applyJoinEvents_append (stepAtomJoinEvents state atom)
          (spineJoinEvents restAtoms (stepAtom state atom)) state.links]

/-- ★ **The whole fold's loop total is the trace's already-connected count** — freshness-threaded (the
cup pairs must test disconnected at every step). -/
theorem processSpine_loops_eq_addJoinEventLoops {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : WireState) →
    WireStateFresh state → 0 < state.nextFresh →
    (processSpine state atoms).loops
      = state.loops + countJoinEventLoops (spineJoinEvents atoms state) state.links
  | [], _, _, _ => (Nat.add_zero _).symm
  | atom :: restAtoms, state, fresh, nfPos => by
      show (processSpine (stepAtom state atom) restAtoms).loops
          = state.loops
            + countJoinEventLoops
                (stepAtomJoinEvents state atom
                  ++ spineJoinEvents restAtoms (stepAtom state atom))
                state.links
      rw [processSpine_loops_eq_addJoinEventLoops restAtoms (stepAtom state atom)
          (stepAtom_wireStateFresh state atom fresh nfPos)
          (Nat.lt_of_lt_of_le nfPos (stepAtom_nextFresh_le state atom)),
        stepAtom_loops_eq_addJoinEventLoops state atom
          (fun edge edgeInLinks => (fresh.2 edge edgeInLinks).1),
        stepAtom_links_eq_applyJoinEvents state atom,
        countJoinEventLoops_append (stepAtomJoinEvents state atom)
          (spineJoinEvents restAtoms (stepAtom state atom)) state.links,
        Nat.add_assoc]

/-- Cell-granularity links faithfulness (the fold over the cell's spine block). -/
theorem runMatchingCell_links_eq_applyJoinEvents {signature : ModeSignature}
    {overallSource overallTarget localSource localTarget : signature.graph.Mode}
    (state : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod) :
    (runMatchingCell state leftAcc rightAcc cell).links
      = applyJoinEvents (spineJoinEvents (cell.spineDiff leftAcc rightAcc []) state)
          state.links :=
  processSpine_links_eq_applyJoinEvents (cell.spineDiff leftAcc rightAcc []) state

/-- Cell-granularity loops faithfulness. -/
theorem runMatchingCell_loops_eq_addJoinEventLoops {signature : ModeSignature}
    {overallSource overallTarget localSource localTarget : signature.graph.Mode}
    (state : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (fresh : WireStateFresh state) (nfPos : 0 < state.nextFresh) :
    (runMatchingCell state leftAcc rightAcc cell).loops
      = state.loops
        + countJoinEventLoops (spineJoinEvents (cell.spineDiff leftAcc rightAcc []) state)
            state.links :=
  processSpine_loops_eq_addJoinEventLoops (cell.spineDiff leftAcc rightAcc []) state fresh nfPos

/-! ## Sigma-equivariance of the event fold -/

/-- ★ **The event fold transports the component view through a pointwise-renamed trace** — iterating
`componentView_unionFindJoin` event by event (forests threaded through the joins).  No injectivity, no
freshness: pure congruence over the sigma-correspondence. -/
theorem componentView_applyJoinEvents (sigma : Nat → Nat) :
    (events : List (Nat × Nat)) → (linksS linksT : List (Nat × Nat)) →
    isUnionFindForest linksS → isUnionFindForest linksT →
    (∀ probeOne probeTwo,
      (unionFindRootOf linksT (sigma probeOne) == unionFindRootOf linksT (sigma probeTwo))
        = (unionFindRootOf linksS probeOne == unionFindRootOf linksS probeTwo)) →
    (probeOne probeTwo : Nat) →
    (unionFindRootOf
        (applyJoinEvents (events.map (fun event => (sigma event.1, sigma event.2))) linksT)
        (sigma probeOne)
      == unionFindRootOf
        (applyJoinEvents (events.map (fun event => (sigma event.1, sigma event.2))) linksT)
        (sigma probeTwo))
    = (unionFindRootOf (applyJoinEvents events linksS) probeOne
      == unionFindRootOf (applyJoinEvents events linksS) probeTwo)
  | [], _, _, _, _, componentComm, probeOne, probeTwo => componentComm probeOne probeTwo
  | (firstNode, secondNode) :: restEvents, linksS, linksT, forestS, forestT, componentComm,
      probeOne, probeTwo =>
      componentView_applyJoinEvents sigma restEvents
        (unionFindJoin linksS firstNode secondNode)
        (unionFindJoin linksT (sigma firstNode) (sigma secondNode))
        (isUnionFindForest_unionFindJoin linksS firstNode secondNode forestS)
        (isUnionFindForest_unionFindJoin linksT (sigma firstNode) (sigma secondNode) forestT)
        (fun innerOne innerTwo => componentView_unionFindJoin sigma linksS linksT forestS forestT
          firstNode secondNode componentComm innerOne innerTwo)
        probeOne probeTwo

/-- ★ **A pointwise-renamed trace closes the same number of loops** — each event's test agrees across
the sigma-correspondence (it IS the correspondence at the event pair), and the correspondence is
maintained through the joins. -/
theorem countJoinEventLoops_map_congr (sigma : Nat → Nat) :
    (events : List (Nat × Nat)) → (linksS linksT : List (Nat × Nat)) →
    isUnionFindForest linksS → isUnionFindForest linksT →
    (∀ probeOne probeTwo,
      (unionFindRootOf linksT (sigma probeOne) == unionFindRootOf linksT (sigma probeTwo))
        = (unionFindRootOf linksS probeOne == unionFindRootOf linksS probeTwo)) →
    countJoinEventLoops (events.map (fun event => (sigma event.1, sigma event.2))) linksT
      = countJoinEventLoops events linksS
  | [], _, _, _, _, _ => rfl
  | (firstNode, secondNode) :: restEvents, linksS, linksT, forestS, forestT, componentComm => by
      show (isSameComponent linksT (sigma firstNode) (sigma secondNode)).toNat
            + countJoinEventLoops
                (restEvents.map (fun event => (sigma event.1, sigma event.2)))
                (unionFindJoin linksT (sigma firstNode) (sigma secondNode))
          = (isSameComponent linksS firstNode secondNode).toNat
              + countJoinEventLoops restEvents (unionFindJoin linksS firstNode secondNode)
      rw [show isSameComponent linksT (sigma firstNode) (sigma secondNode)
            = isSameComponent linksS firstNode secondNode from
          componentComm firstNode secondNode,
        countJoinEventLoops_map_congr sigma restEvents
          (unionFindJoin linksS firstNode secondNode)
          (unionFindJoin linksT (sigma firstNode) (sigma secondNode))
          (isUnionFindForest_unionFindJoin linksS firstNode secondNode forestS)
          (isUnionFindForest_unionFindJoin linksT (sigma firstNode) (sigma secondNode) forestT)
          (fun innerOne innerTwo => componentView_unionFindJoin sigma linksS linksT forestS
            forestT firstNode secondNode componentComm innerOne innerTwo)]

/-! ## Honesty marker -/

/-- **Honesty marker — the join-event trace is REIFIED and the fold is FAITHFUL to it.**  Every
matching-fold run's `links` output is the homogeneous join fold over its event trace
(`processSpine_links_eq_applyJoinEvents`, unconditional via the cap's redundant outer test), and its
loop total is the trace's already-connected count (`processSpine_loops_eq_addJoinEventLoops`,
freshness-conditioned via the out-of-support root identity).  The event fold is sigma-equivariant at
the component-view and loop-count levels (`componentView_applyJoinEvents`,
`countJoinEventLoops_map_congr`).  NOT yet covered: the pure EXCHANGE of two event blocks at fixed
ids (view and count invariance under transposing concatenated traces — the Mazurkiewicz content, via
the banked universal-property kit), and the sigma-correspondence of the two orders' traces themselves
(the wire-side event congruence) — the next bricks of the sigma witness.  `= true`. -/
def fxMode_hasMatchingJoinEventReification : Bool := true

end FX1Poly.Polygraph
