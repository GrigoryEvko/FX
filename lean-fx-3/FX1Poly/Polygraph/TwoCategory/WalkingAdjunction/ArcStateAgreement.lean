import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # WalkingAdjunction/ArcStateAgreement — the order-insensitive state-agreement vehicle

The CAP x CAP obstruction (`ArcCapCapSwapObstruction`) proved that no renaming `sigma` relates the
two run orders of a cap-cap disjoint-window swap: the merged component's union-find REPRESENTATIVE
is order-dependent.  What survives is everything the extract actually reads — and for a cap-cap
swap the two orders even agree on the nose in every field EXCEPT the link list, whose PARTITION
(the `isSameComponent` relation) coincides while its representatives differ.

This file builds that replacement vehicle:

  * `ArcStateAgree` — equal open wires / fresh counter / loops / event LISTS, plus
    partition-equal links (and the forest side-conditions the join formula needs);
  * `isSameComponent_unionFindJoin_congr` — the crux: joining the SAME two nodes over two
    partition-equal forests yields partition-equal results, because the post-join same-component
    relation is a function of pre-join same-component queries only (the representative drops out);
  * `arcStateAgree_stepArcAtom` / `arcStateAgree_processArcSpine` / `arcStateAgree_runArcCell` —
    the invariant is step-stable and folds over any common suffix: every step reads the states
    only through equal wire lists, equal counters, and same-component queries;
  * `sameArcPartition_of_arcStateAgree` + `extractArc_eq_of_arcStateAgree` — the readout: agreeing
    states have the same partition view, hence EQUAL arc extracts.

The remaining cap-cap-specific brick is the core lemma that the two run orders of a cap-cap
disjoint-window swap ARE `ArcStateAgree` (partition join-commutation + the loop rank argument);
this file supplies everything downstream of that core. -/

namespace FX1Poly.Polygraph

/-- ★ **The state-agreement invariant** — the order-insensitive replacement for `ArcStepSimCount`
on the cap-cap leg.  Two arc states agree when every field is EQUAL except the link list, and the
link lists induce the SAME component relation (their union-find representatives may differ).  The
forest fields carry the side-condition the join root formula (`unionFindRootOf_unionFindJoin`)
needs for step-stability. -/
structure ArcStateAgree (stateS stateT : ArcWireState) : Prop where
  /-- The open-wire lists are equal (cap-cap allocation order is event-only). -/
  openEq : stateS.openWires = stateT.openWires
  /-- The fresh-allocation counters are equal. -/
  nfEq : stateS.nextFresh = stateT.nextFresh
  /-- The loop counts are equal. -/
  loopsEq : stateS.loops = stateT.loops
  /-- The cup-event lists are equal AS LISTS (same allocation order). -/
  cupEventsEq : stateS.cupEventNodes = stateT.cupEventNodes
  /-- The cap-event lists are equal AS LISTS. -/
  capEventsEq : stateS.capEventNodes = stateT.capEventNodes
  /-- The link lists are partition-equal: every same-component query agrees. -/
  componentsEq : ∀ probeLeft probeRight,
      isSameComponent stateS.links probeLeft probeRight
        = isSameComponent stateT.links probeLeft probeRight
  /-- The first link list is a forest. -/
  forestS : isUnionFindForest stateS.links
  /-- The second link list is a forest. -/
  forestT : isUnionFindForest stateT.links

/-- ★ **Joining the same two nodes preserves partition-equality** — the vehicle's crux.  Over a
forest, `unionFindRootOf_unionFindJoin` expresses each post-join root as an `if` on pre-join root
equalities, so the post-join same-component boolean is a combination of PRE-join same-component
queries: the guards are `componentsAgree firstNode _` instances and every leaf is a
`componentsAgree _ _` instance.  The divergent representative never appears — exactly why the
partition survives the CAP x CAP obstruction that kills the renaming. -/
theorem isSameComponent_unionFindJoin_congr (linksS linksT : List (Nat × Nat))
    (forestS : isUnionFindForest linksS) (forestT : isUnionFindForest linksT)
    (componentsAgree : ∀ probeLeft probeRight,
      isSameComponent linksS probeLeft probeRight = isSameComponent linksT probeLeft probeRight)
    (firstNode secondNode queryLeft queryRight : Nat) :
    isSameComponent (unionFindJoin linksS firstNode secondNode) queryLeft queryRight
      = isSameComponent (unionFindJoin linksT firstNode secondNode) queryLeft queryRight := by
  show (unionFindRootOf (unionFindJoin linksS firstNode secondNode) queryLeft
          == unionFindRootOf (unionFindJoin linksS firstNode secondNode) queryRight)
     = (unionFindRootOf (unionFindJoin linksT firstNode secondNode) queryLeft
          == unionFindRootOf (unionFindJoin linksT firstNode secondNode) queryRight)
  rw [unionFindRootOf_unionFindJoin linksS firstNode secondNode queryLeft forestS,
    unionFindRootOf_unionFindJoin linksS firstNode secondNode queryRight forestS,
    unionFindRootOf_unionFindJoin linksT firstNode secondNode queryLeft forestT,
    unionFindRootOf_unionFindJoin linksT firstNode secondNode queryRight forestT]
  have guardLeftAgree : (unionFindRootOf linksS firstNode == unionFindRootOf linksS queryLeft)
      = (unionFindRootOf linksT firstNode == unionFindRootOf linksT queryLeft) :=
    componentsAgree firstNode queryLeft
  have guardRightAgree : (unionFindRootOf linksS firstNode == unionFindRootOf linksS queryRight)
      = (unionFindRootOf linksT firstNode == unionFindRootOf linksT queryRight) :=
    componentsAgree firstNode queryRight
  rw [guardLeftAgree, guardRightAgree]
  cases guardLeft : (unionFindRootOf linksT firstNode == unionFindRootOf linksT queryLeft) with
  | true =>
      cases guardRight : (unionFindRootOf linksT firstNode == unionFindRootOf linksT queryRight) with
      | true => exact componentsAgree secondNode secondNode
      | false => exact componentsAgree secondNode queryRight
  | false =>
      cases guardRight : (unionFindRootOf linksT firstNode == unionFindRootOf linksT queryRight) with
      | true => exact componentsAgree queryLeft secondNode
      | false => exact componentsAgree queryLeft queryRight

/-- A CUP step preserves state agreement: the inserted block, the counter bump and the prepended
event are EQUAL on both sides (`openEq`/`nfEq`), and the two nested joins act on the same node
values, so partition-equality transports through `isSameComponent_unionFindJoin_congr` twice. -/
theorem arcStateAgree_stepCupArc (stateS stateT : ArcWireState) (position : Nat)
    (agree : ArcStateAgree stateS stateT) :
    ArcStateAgree (stepCupArc stateS position) (stepCupArc stateT position) where
  openEq := by
    show natListInsertAt stateS.openWires position [stateS.nextFresh, stateS.nextFresh + 1]
       = natListInsertAt stateT.openWires position [stateT.nextFresh, stateT.nextFresh + 1]
    rw [agree.openEq, agree.nfEq]
  nfEq := by
    show stateS.nextFresh + 3 = stateT.nextFresh + 3
    rw [agree.nfEq]
  loopsEq := agree.loopsEq
  cupEventsEq := by
    show (stateS.nextFresh + 2) :: stateS.cupEventNodes = (stateT.nextFresh + 2) :: stateT.cupEventNodes
    rw [agree.nfEq, agree.cupEventsEq]
  capEventsEq := agree.capEventsEq
  componentsEq := by
    intro probeLeft probeRight
    show isSameComponent
        (unionFindJoin (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
          (stateS.nextFresh + 2) stateS.nextFresh) probeLeft probeRight
      = isSameComponent
        (unionFindJoin (unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1))
          (stateT.nextFresh + 2) stateT.nextFresh) probeLeft probeRight
    rw [← agree.nfEq]
    exact isSameComponent_unionFindJoin_congr
      (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
      (unionFindJoin stateT.links stateS.nextFresh (stateS.nextFresh + 1))
      (isUnionFindForest_unionFindJoin _ _ _ agree.forestS)
      (isUnionFindForest_unionFindJoin _ _ _ agree.forestT)
      (fun innerLeft innerRight => isSameComponent_unionFindJoin_congr stateS.links stateT.links
        agree.forestS agree.forestT agree.componentsEq stateS.nextFresh (stateS.nextFresh + 1)
        innerLeft innerRight)
      (stateS.nextFresh + 2) stateS.nextFresh probeLeft probeRight
  forestS := isUnionFindForest_stepCupArc stateS position agree.forestS
  forestT := isUnionFindForest_stepCupArc stateT position agree.forestT

/-- A CAP step preserves state agreement: both sides read the SAME wire values (`openEq`), the
loop increment's guard is a same-component query (`componentsEq`), the event allocation is equal
(`nfEq`), and the two nested joins act on the same node values. -/
theorem arcStateAgree_stepCapArc (stateS stateT : ArcWireState) (position : Nat)
    (agree : ArcStateAgree stateS stateT) :
    ArcStateAgree (stepCapArc stateS position) (stepCapArc stateT position) where
  openEq := by
    show natListRemoveTwoAt stateS.openWires position = natListRemoveTwoAt stateT.openWires position
    rw [agree.openEq]
  nfEq := by
    show stateS.nextFresh + 1 = stateT.nextFresh + 1
    rw [agree.nfEq]
  loopsEq := by
    show (if isSameComponent stateS.links (natListGetAt stateS.openWires position)
              (natListGetAt stateS.openWires (position + 1))
            then stateS.loops + 1 else stateS.loops)
       = (if isSameComponent stateT.links (natListGetAt stateT.openWires position)
              (natListGetAt stateT.openWires (position + 1))
            then stateT.loops + 1 else stateT.loops)
    rw [← agree.openEq,
      agree.componentsEq (natListGetAt stateS.openWires position)
        (natListGetAt stateS.openWires (position + 1)),
      agree.loopsEq]
  cupEventsEq := agree.cupEventsEq
  capEventsEq := by
    show stateS.nextFresh :: stateS.capEventNodes = stateT.nextFresh :: stateT.capEventNodes
    rw [agree.nfEq, agree.capEventsEq]
  componentsEq := by
    intro probeLeft probeRight
    show isSameComponent
        (unionFindJoin (unionFindJoin stateS.links (natListGetAt stateS.openWires position)
            (natListGetAt stateS.openWires (position + 1))) stateS.nextFresh
          (natListGetAt stateS.openWires position)) probeLeft probeRight
      = isSameComponent
        (unionFindJoin (unionFindJoin stateT.links (natListGetAt stateT.openWires position)
            (natListGetAt stateT.openWires (position + 1))) stateT.nextFresh
          (natListGetAt stateT.openWires position)) probeLeft probeRight
    rw [← agree.openEq, ← agree.nfEq]
    exact isSameComponent_unionFindJoin_congr
      (unionFindJoin stateS.links (natListGetAt stateS.openWires position)
        (natListGetAt stateS.openWires (position + 1)))
      (unionFindJoin stateT.links (natListGetAt stateS.openWires position)
        (natListGetAt stateS.openWires (position + 1)))
      (isUnionFindForest_unionFindJoin _ _ _ agree.forestS)
      (isUnionFindForest_unionFindJoin _ _ _ agree.forestT)
      (fun innerLeft innerRight => isSameComponent_unionFindJoin_congr stateS.links stateT.links
        agree.forestS agree.forestT agree.componentsEq
        (natListGetAt stateS.openWires position) (natListGetAt stateS.openWires (position + 1))
        innerLeft innerRight)
      stateS.nextFresh (natListGetAt stateS.openWires position) probeLeft probeRight
  forestS := isUnionFindForest_stepCapArc stateS position agree.forestS
  forestT := isUnionFindForest_stepCapArc stateT position agree.forestT

/-- ★ **One arc step preserves state agreement** — cup / cap via the arm lemmas; the box arm
changes no links and applies the same wire/counter surgery to both (equal) sides. -/
theorem arcStateAgree_stepArcAtom {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (agree : ArcStateAgree stateS stateT) :
    ArcStateAgree (stepArcAtom stateS atom) (stepArcAtom stateT atom) := by
  unfold stepArcAtom
  split
  · exact arcStateAgree_stepCupArc stateS stateT atom.leftContext.length agree
  · exact arcStateAgree_stepCapArc stateS stateT atom.leftContext.length agree
  · refine ⟨?_, ?_, agree.loopsEq, agree.cupEventsEq, agree.capEventsEq,
      agree.componentsEq, agree.forestS, agree.forestT⟩
    · rw [agree.openEq, agree.nfEq]
    · rw [agree.nfEq]

/-- ★ **State agreement folds over a spine** — structural recursion threading
`arcStateAgree_stepArcAtom` through each common atom. -/
theorem arcStateAgree_processArcSpine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (stateS stateT : ArcWireState) →
    ArcStateAgree stateS stateT →
    ArcStateAgree (processArcSpine stateS atoms) (processArcSpine stateT atoms)
  | [], _, _, agree => agree
  | atom :: rest, stateS, stateT, agree => by
      show ArcStateAgree (processArcSpine (stepArcAtom stateS atom) rest)
        (processArcSpine (stepArcAtom stateT atom) rest)
      exact arcStateAgree_processArcSpine rest (stepArcAtom stateS atom) (stepArcAtom stateT atom)
        (arcStateAgree_stepArcAtom stateS stateT atom agree)

/-- State agreement survives running one cell — the suffix-peel leg of the agreement vehicle. -/
theorem arcStateAgree_runArcCell {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (stateS stateT : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (agree : ArcStateAgree stateS stateT) :
    ArcStateAgree (runArcCell stateS leftAcc rightAcc cell) (runArcCell stateT leftAcc rightAcc cell) :=
  arcStateAgree_processArcSpine (cell.spineDiff leftAcc rightAcc []) stateS stateT agree

/-- `countEventsInRoot` at a PORT'S OWN root is a partition-level read: each event contributes iff
it is same-component with the port, so partition-equal links give equal counts over the same event
list.  This is exactly the quantity where the CAP x CAP representative divergence cancels. -/
theorem countEventsInRoot_atPortRoot_congr (linksS linksT : List (Nat × Nat))
    (componentsAgree : ∀ probeLeft probeRight,
      isSameComponent linksS probeLeft probeRight = isSameComponent linksT probeLeft probeRight)
    (port : Nat) :
    (events : List Nat) →
    countEventsInRoot linksS (unionFindRootOf linksS port) events
      = countEventsInRoot linksT (unionFindRootOf linksT port) events
  | [] => rfl
  | eventNode :: rest => by
      show (if unionFindRootOf linksS eventNode == unionFindRootOf linksS port then 1 else 0)
          + countEventsInRoot linksS (unionFindRootOf linksS port) rest
        = (if unionFindRootOf linksT eventNode == unionFindRootOf linksT port then 1 else 0)
          + countEventsInRoot linksT (unionFindRootOf linksT port) rest
      have guardAgree : (unionFindRootOf linksS eventNode == unionFindRootOf linksS port)
          = (unionFindRootOf linksT eventNode == unionFindRootOf linksT port) :=
        componentsAgree eventNode port
      rw [guardAgree, countEventsInRoot_atPortRoot_congr linksS linksT componentsAgree port rest]

/-- ★ **Agreeing states share the partition view** — the readout to `SameArcPartition`: lengths and
loops from the equal fields, the boundary same-component booleans from `componentsEq` over the
equal boundary node lists, and the per-port event counts from the partition-level count congruence
over the equal event lists. -/
theorem sameArcPartition_of_arcStateAgree (bottomCount : Nat) (stateS stateT : ArcWireState)
    (agree : ArcStateAgree stateS stateT) : SameArcPartition bottomCount stateS stateT := by
  have boundaryEq : boundaryNodesOf bottomCount stateS = boundaryNodesOf bottomCount stateT := by
    show List.range bottomCount ++ stateS.openWires = List.range bottomCount ++ stateT.openWires
    rw [agree.openEq]
  refine ⟨congrArg List.length agree.openEq, agree.loopsEq, ?_, ?_, ?_⟩
  · intro firstIndex secondIndex _ _
    show isSameComponent stateS.links
        (natListGetAt (boundaryNodesOf bottomCount stateS) firstIndex)
        (natListGetAt (boundaryNodesOf bottomCount stateS) secondIndex)
      = isSameComponent stateT.links
        (natListGetAt (boundaryNodesOf bottomCount stateT) firstIndex)
        (natListGetAt (boundaryNodesOf bottomCount stateT) secondIndex)
    rw [boundaryEq]
    exact agree.componentsEq
      (natListGetAt (boundaryNodesOf bottomCount stateT) firstIndex)
      (natListGetAt (boundaryNodesOf bottomCount stateT) secondIndex)
  · intro index _
    show countEventsInRoot stateS.links
        (unionFindRootOf stateS.links (natListGetAt (boundaryNodesOf bottomCount stateS) index))
        stateS.cupEventNodes
      = countEventsInRoot stateT.links
        (unionFindRootOf stateT.links (natListGetAt (boundaryNodesOf bottomCount stateT) index))
        stateT.cupEventNodes
    rw [boundaryEq, ← agree.cupEventsEq]
    exact countEventsInRoot_atPortRoot_congr stateS.links stateT.links agree.componentsEq
      (natListGetAt (boundaryNodesOf bottomCount stateT) index) stateS.cupEventNodes
  · intro index _
    show countEventsInRoot stateS.links
        (unionFindRootOf stateS.links (natListGetAt (boundaryNodesOf bottomCount stateS) index))
        stateS.capEventNodes
      = countEventsInRoot stateT.links
        (unionFindRootOf stateT.links (natListGetAt (boundaryNodesOf bottomCount stateT) index))
        stateT.capEventNodes
    rw [boundaryEq, ← agree.capEventsEq]
    exact countEventsInRoot_atPortRoot_congr stateS.links stateT.links agree.componentsEq
      (natListGetAt (boundaryNodesOf bottomCount stateT) index) stateS.capEventNodes

/-- ★ **Agreeing states have EQUAL arc extracts** — the agreement vehicle's destination, via
`extractArc_eq_of_sameArcPartition` with the event-count legs read off the equal event lists. -/
theorem extractArc_eq_of_arcStateAgree (bottomCount : Nat) (stateS stateT : ArcWireState)
    (agree : ArcStateAgree stateS stateT) :
    extractArc bottomCount stateS = extractArc bottomCount stateT :=
  extractArc_eq_of_sameArcPartition bottomCount stateS stateT
    (sameArcPartition_of_arcStateAgree bottomCount stateS stateT agree)
    (congrArg List.length agree.cupEventsEq) (congrArg List.length agree.capEventsEq)

/-- **Honesty marker — the state-agreement VEHICLE is BUILT.**  `ArcStateAgree` is step-stable
(`arcStateAgree_stepArcAtom`), folds over any common suffix (`arcStateAgree_processArcSpine` /
`arcStateAgree_runArcCell`), and reads out to equal extracts (`extractArc_eq_of_arcStateAgree`).
This is the order-insensitive replacement the CAP x CAP obstruction
(`fxMode_hasCapCapRenameObstruction`) demanded.  What this marker does NOT claim: the cap-cap
CORE agreement itself — that the two run orders of a cap-cap disjoint-window swap are
`ArcStateAgree` (partition join-commutation + the loop rank argument) — which is the next brick.
`= true` records vehicle availability only. -/
def fxMode_hasArcStateAgreementVehicle : Bool := true

end FX1Poly.Polygraph
