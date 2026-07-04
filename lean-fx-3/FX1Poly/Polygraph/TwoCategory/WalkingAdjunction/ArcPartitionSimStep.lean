import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPartitionSimulation

/-! # WalkingAdjunction/ArcPartitionSimStep — the partition simulation's join substrate

Step-stability of `ArcPartitionSim` needs its two rootComm-free fields pushed through a
`unionFindJoin` — the cap MERGE being the hard case.  This file ships the two join-level
transports:

  * `isSameComponent_unionFindJoin_sigmaCorr` — the `sigma`-twisted version of the beta4a
    join-congruence crux: joining `sigma`-image nodes on the target preserves the
    `componentsCorr` correspondence.  Pure guard bookkeeping over the after-join root formula;
    every leaf is a `componentsCorr` instance.
  * `countEventsInRoot_unionFindJoin_partitionMatch` — the PARTITION-keyed count transport,
    replacing the rootComm-keyed `countEventsInRoot_unionFindJoin_sigmaMatch`: given
    `componentsCorr` and the per-probe count correspondence, the corresponding join preserves
    the per-probe PORT-ROOTED counts.  Dispatch: joined-roots-equal makes both joins no-ops;
    a real merge sends probes in either merged component to the summed count
    (`countEventsInRoot_unionFindJoin_target` on both sides, matched through the count
    correspondence at the two join probes) and unaffected probes to their old count
    (`_other` on both sides).  No root VALUE ever crosses between the two states. -/

namespace FX1Poly.Polygraph

/-- ★ **The `sigma`-twisted join congruence** — `componentsCorr` survives a corresponding join.
Joining `sigma firstNode, sigma secondNode` on the target and `firstNode, secondNode` on the
source preserves the `sigma`-conjugated same-component correspondence.  After-join roots via
`unionFindRootOf_unionFindJoin` on both sides; the two guards transport by `componentsCorr`
(ascribed to the `==` spelling by defeq), and each of the four guard leaves is again a
`componentsCorr` instance. -/
theorem isSameComponent_unionFindJoin_sigmaCorr (sigma : Nat → Nat)
    (linksS linksT : List (Nat × Nat))
    (forestS : isUnionFindForest linksS) (forestT : isUnionFindForest linksT)
    (componentsCorr : ∀ probeLeft probeRight,
      isSameComponent linksT (sigma probeLeft) (sigma probeRight)
        = isSameComponent linksS probeLeft probeRight)
    (firstNode secondNode queryLeft queryRight : Nat) :
    isSameComponent (unionFindJoin linksT (sigma firstNode) (sigma secondNode))
        (sigma queryLeft) (sigma queryRight)
      = isSameComponent (unionFindJoin linksS firstNode secondNode) queryLeft queryRight := by
  show (unionFindRootOf (unionFindJoin linksT (sigma firstNode) (sigma secondNode)) (sigma queryLeft)
          == unionFindRootOf (unionFindJoin linksT (sigma firstNode) (sigma secondNode))
              (sigma queryRight))
     = (unionFindRootOf (unionFindJoin linksS firstNode secondNode) queryLeft
          == unionFindRootOf (unionFindJoin linksS firstNode secondNode) queryRight)
  rw [unionFindRootOf_unionFindJoin linksT (sigma firstNode) (sigma secondNode)
      (sigma queryLeft) forestT,
    unionFindRootOf_unionFindJoin linksT (sigma firstNode) (sigma secondNode)
      (sigma queryRight) forestT,
    unionFindRootOf_unionFindJoin linksS firstNode secondNode queryLeft forestS,
    unionFindRootOf_unionFindJoin linksS firstNode secondNode queryRight forestS]
  have guardLeftCorr : (unionFindRootOf linksT (sigma firstNode)
        == unionFindRootOf linksT (sigma queryLeft))
      = (unionFindRootOf linksS firstNode == unionFindRootOf linksS queryLeft) :=
    componentsCorr firstNode queryLeft
  have guardRightCorr : (unionFindRootOf linksT (sigma firstNode)
        == unionFindRootOf linksT (sigma queryRight))
      = (unionFindRootOf linksS firstNode == unionFindRootOf linksS queryRight) :=
    componentsCorr firstNode queryRight
  rw [guardLeftCorr, guardRightCorr]
  cases guardLeft : (unionFindRootOf linksS firstNode == unionFindRootOf linksS queryLeft) with
  | true =>
      cases guardRight : (unionFindRootOf linksS firstNode
          == unionFindRootOf linksS queryRight) with
      | true => exact componentsCorr secondNode secondNode
      | false => exact componentsCorr secondNode queryRight
  | false =>
      cases guardRight : (unionFindRootOf linksS firstNode
          == unionFindRootOf linksS queryRight) with
      | true => exact componentsCorr queryLeft secondNode
      | false => exact componentsCorr queryLeft queryRight

/-- ★ **The PARTITION-keyed count transport through a corresponding join** — the rootComm-free
replacement for `countEventsInRoot_unionFindJoin_sigmaMatch`.  If the joined roots already
coincide (guard transported by `componentsCorr`), both joins are no-ops and the pre-join
correspondence closes.  On a real merge, a probe in either merged component reads the SUMMED
count on both sides (`countEventsInRoot_unionFindJoin_target`, matched through `countCorr` at
the two join probes); an unaffected probe keeps its old count (`_other`).  The case selection
transports by `componentsCorr`, so no root value is ever compared across the two states. -/
theorem countEventsInRoot_unionFindJoin_partitionMatch (sigma : Nat → Nat)
    (linksS linksT : List (Nat × Nat))
    (forestS : isUnionFindForest linksS) (forestT : isUnionFindForest linksT)
    (firstS secondS : Nat)
    (componentsCorr : ∀ probeLeft probeRight,
      isSameComponent linksT (sigma probeLeft) (sigma probeRight)
        = isSameComponent linksS probeLeft probeRight)
    (eventsS eventsT : List Nat)
    (countCorr : ∀ probe,
      countEventsInRoot linksT (unionFindRootOf linksT (sigma probe)) eventsT
        = countEventsInRoot linksS (unionFindRootOf linksS probe) eventsS) :
    ∀ probe,
      countEventsInRoot (unionFindJoin linksT (sigma firstS) (sigma secondS))
          (unionFindRootOf (unionFindJoin linksT (sigma firstS) (sigma secondS)) (sigma probe))
          eventsT
        = countEventsInRoot (unionFindJoin linksS firstS secondS)
            (unionFindRootOf (unionFindJoin linksS firstS secondS) probe) eventsS := by
  intro probe
  have guardJoin : (unionFindRootOf linksT (sigma firstS)
        == unionFindRootOf linksT (sigma secondS))
      = (unionFindRootOf linksS firstS == unionFindRootOf linksS secondS) :=
    componentsCorr firstS secondS
  cases joinedSame : (unionFindRootOf linksS firstS == unionFindRootOf linksS secondS) with
  | true =>
      have joinNoOpS : unionFindJoin linksS firstS secondS = linksS := by
        show (if unionFindRootOf linksS firstS == unionFindRootOf linksS secondS then linksS
              else (unionFindRootOf linksS firstS, unionFindRootOf linksS secondS) :: linksS)
           = linksS
        rw [joinedSame]; rfl
      have joinedSameT : (unionFindRootOf linksT (sigma firstS)
          == unionFindRootOf linksT (sigma secondS)) = true := by
        rw [guardJoin]; exact joinedSame
      have joinNoOpT : unionFindJoin linksT (sigma firstS) (sigma secondS) = linksT := by
        show (if unionFindRootOf linksT (sigma firstS) == unionFindRootOf linksT (sigma secondS)
              then linksT
              else (unionFindRootOf linksT (sigma firstS),
                unionFindRootOf linksT (sigma secondS)) :: linksT)
           = linksT
        rw [joinedSameT]; rfl
      rw [joinNoOpS, joinNoOpT]
      exact countCorr probe
  | false =>
      have rootsDistinctS : (unionFindRootOf linksS firstS
          == unionFindRootOf linksS secondS) = true → False := by
        rw [joinedSame]; exact fun contra => Bool.noConfusion contra
      have rootsDistinctT : (unionFindRootOf linksT (sigma firstS)
          == unionFindRootOf linksT (sigma secondS)) = true → False := by
        rw [guardJoin, joinedSame]; exact fun contra => Bool.noConfusion contra
      rw [unionFindRootOf_unionFindJoin linksT (sigma firstS) (sigma secondS)
          (sigma probe) forestT,
        unionFindRootOf_unionFindJoin linksS firstS secondS probe forestS]
      have guardFirstProbe : (unionFindRootOf linksT (sigma firstS)
            == unionFindRootOf linksT (sigma probe))
          = (unionFindRootOf linksS firstS == unionFindRootOf linksS probe) :=
        componentsCorr firstS probe
      rw [guardFirstProbe]
      cases probeInFirst : (unionFindRootOf linksS firstS == unionFindRootOf linksS probe) with
      | true =>
          show countEventsInRoot (unionFindJoin linksT (sigma firstS) (sigma secondS))
              (unionFindRootOf linksT (sigma secondS)) eventsT
            = countEventsInRoot (unionFindJoin linksS firstS secondS)
                (unionFindRootOf linksS secondS) eventsS
          rw [countEventsInRoot_unionFindJoin_target linksT (sigma firstS) (sigma secondS)
              forestT rootsDistinctT eventsT,
            countEventsInRoot_unionFindJoin_target linksS firstS secondS
              forestS rootsDistinctS eventsS,
            countCorr firstS, countCorr secondS]
      | false =>
          have guardSecondProbe : (unionFindRootOf linksT (sigma secondS)
                == unionFindRootOf linksT (sigma probe))
              = (unionFindRootOf linksS secondS == unionFindRootOf linksS probe) :=
            componentsCorr secondS probe
          cases probeInSecond : (unionFindRootOf linksS secondS
              == unionFindRootOf linksS probe) with
          | true =>
              have rootShiftS : unionFindRootOf linksS secondS = unionFindRootOf linksS probe :=
                of_decide_eq_true probeInSecond
              have probeInSecondT : (unionFindRootOf linksT (sigma secondS)
                  == unionFindRootOf linksT (sigma probe)) = true := by
                rw [guardSecondProbe]; exact probeInSecond
              have rootShiftT : unionFindRootOf linksT (sigma secondS)
                  = unionFindRootOf linksT (sigma probe) :=
                of_decide_eq_true probeInSecondT
              show countEventsInRoot (unionFindJoin linksT (sigma firstS) (sigma secondS))
                  (unionFindRootOf linksT (sigma probe)) eventsT
                = countEventsInRoot (unionFindJoin linksS firstS secondS)
                    (unionFindRootOf linksS probe) eventsS
              rw [← rootShiftS, ← rootShiftT,
                countEventsInRoot_unionFindJoin_target linksT (sigma firstS) (sigma secondS)
                  forestT rootsDistinctT eventsT,
                countEventsInRoot_unionFindJoin_target linksS firstS secondS
                  forestS rootsDistinctS eventsS,
                countCorr firstS, countCorr secondS]
          | false =>
              have probeOutFirstT : (unionFindRootOf linksT (sigma firstS)
                  == unionFindRootOf linksT (sigma probe)) = false := by
                rw [guardFirstProbe]; exact probeInFirst
              have probeOutSecondT : (unionFindRootOf linksT (sigma secondS)
                  == unionFindRootOf linksT (sigma probe)) = false := by
                rw [guardSecondProbe]; exact probeInSecond
              show countEventsInRoot (unionFindJoin linksT (sigma firstS) (sigma secondS))
                  (unionFindRootOf linksT (sigma probe)) eventsT
                = countEventsInRoot (unionFindJoin linksS firstS secondS)
                    (unionFindRootOf linksS probe) eventsS
              rw [countEventsInRoot_unionFindJoin_other linksT (sigma firstS) (sigma secondS)
                  (unionFindRootOf linksT (sigma probe)) forestT
                  probeOutFirstT probeOutSecondT eventsT,
                countEventsInRoot_unionFindJoin_other linksS firstS secondS
                  (unionFindRootOf linksS probe) forestS probeInFirst probeInSecond eventsS]
              exact countCorr probe

/-- ★ **`componentsCorr` survives one arc step** — freshness-free.  CUP: the two nested joins act
at fresh nodes (`nf`, `nf + 1`, `nf + 2`), all `sigma`-fixed by `fixesAbove`, so two
`isSameComponent_unionFindJoin_sigmaCorr` applications transport the correspondence.  CAP: the
join nodes are the two read wires — `sigma`-images of the source wires by `openMap` — plus the
`sigma`-fixed fresh event node.  BOX: links untouched.  Unlike the rootComm-keyed step, NO
`ArcStateFresh` and no `0 < nextFresh` is consumed anywhere. -/
theorem stepArcAtom_componentsCorr {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (forestS : isUnionFindForest stateS.links) (forestT : isUnionFindForest stateT.links)
    (nfEq : stateS.nextFresh = stateT.nextFresh)
    (openMap : stateT.openWires = stateS.openWires.map sigma)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (componentsCorr : ∀ probeLeft probeRight,
      isSameComponent stateT.links (sigma probeLeft) (sigma probeRight)
        = isSameComponent stateS.links probeLeft probeRight) :
    ∀ probeLeft probeRight,
      isSameComponent (stepArcAtom stateT atom).links (sigma probeLeft) (sigma probeRight)
        = isSameComponent (stepArcAtom stateS atom).links probeLeft probeRight := by
  intro probeLeft probeRight
  have fixNf : sigma stateS.nextFresh = stateS.nextFresh :=
    fixesAbove stateS.nextFresh (Nat.le_refl _)
  have fixNfOne : sigma (stateS.nextFresh + 1) = stateS.nextFresh + 1 :=
    fixesAbove (stateS.nextFresh + 1) (Nat.le_add_right _ _)
  have fixNfTwo : sigma (stateS.nextFresh + 2) = stateS.nextFresh + 2 :=
    fixesAbove (stateS.nextFresh + 2) (Nat.le_add_right _ _)
  unfold stepArcAtom
  split
  · show isSameComponent
        (unionFindJoin (unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1))
          (stateT.nextFresh + 2) stateT.nextFresh) (sigma probeLeft) (sigma probeRight)
      = isSameComponent
        (unionFindJoin (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
          (stateS.nextFresh + 2) stateS.nextFresh) probeLeft probeRight
    rw [← nfEq]
    have innerCorr : ∀ queryLeft queryRight,
        isSameComponent (unionFindJoin stateT.links stateS.nextFresh (stateS.nextFresh + 1))
            (sigma queryLeft) (sigma queryRight)
          = isSameComponent (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
              queryLeft queryRight := by
      intro queryLeft queryRight
      have twisted := isSameComponent_unionFindJoin_sigmaCorr sigma stateS.links stateT.links
        forestS forestT componentsCorr stateS.nextFresh (stateS.nextFresh + 1)
        queryLeft queryRight
      rw [fixNf, fixNfOne] at twisted
      exact twisted
    have outerCorr := isSameComponent_unionFindJoin_sigmaCorr sigma
      (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
      (unionFindJoin stateT.links stateS.nextFresh (stateS.nextFresh + 1))
      (isUnionFindForest_unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1)
        forestS)
      (isUnionFindForest_unionFindJoin stateT.links stateS.nextFresh (stateS.nextFresh + 1)
        forestT)
      innerCorr (stateS.nextFresh + 2) stateS.nextFresh probeLeft probeRight
    rw [fixNfTwo, fixNf] at outerCorr
    exact outerCorr
  · have wireLeft : natListGetAt stateT.openWires atom.leftContext.length
        = sigma (natListGetAt stateS.openWires atom.leftContext.length) := by
      rw [openMap, natListGetAt_map sigma sigmaFixesZero]
    have wireRight : natListGetAt stateT.openWires (atom.leftContext.length + 1)
        = sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1)) := by
      rw [openMap, natListGetAt_map sigma sigmaFixesZero]
    show isSameComponent
        (unionFindJoin (unionFindJoin stateT.links
            (natListGetAt stateT.openWires atom.leftContext.length)
            (natListGetAt stateT.openWires (atom.leftContext.length + 1)))
          stateT.nextFresh (natListGetAt stateT.openWires atom.leftContext.length))
        (sigma probeLeft) (sigma probeRight)
      = isSameComponent
        (unionFindJoin (unionFindJoin stateS.links
            (natListGetAt stateS.openWires atom.leftContext.length)
            (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
          stateS.nextFresh (natListGetAt stateS.openWires atom.leftContext.length))
        probeLeft probeRight
    rw [← nfEq, wireLeft, wireRight]
    have innerCorr : ∀ queryLeft queryRight,
        isSameComponent (unionFindJoin stateT.links
            (sigma (natListGetAt stateS.openWires atom.leftContext.length))
            (sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1))))
            (sigma queryLeft) (sigma queryRight)
          = isSameComponent (unionFindJoin stateS.links
              (natListGetAt stateS.openWires atom.leftContext.length)
              (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
              queryLeft queryRight :=
      fun queryLeft queryRight =>
        isSameComponent_unionFindJoin_sigmaCorr sigma stateS.links stateT.links forestS forestT
          componentsCorr (natListGetAt stateS.openWires atom.leftContext.length)
          (natListGetAt stateS.openWires (atom.leftContext.length + 1)) queryLeft queryRight
    have outerCorr := isSameComponent_unionFindJoin_sigmaCorr sigma
      (unionFindJoin stateS.links (natListGetAt stateS.openWires atom.leftContext.length)
        (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
      (unionFindJoin stateT.links
        (sigma (natListGetAt stateS.openWires atom.leftContext.length))
        (sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1))))
      (isUnionFindForest_unionFindJoin stateS.links
        (natListGetAt stateS.openWires atom.leftContext.length)
        (natListGetAt stateS.openWires (atom.leftContext.length + 1)) forestS)
      (isUnionFindForest_unionFindJoin stateT.links
        (sigma (natListGetAt stateS.openWires atom.leftContext.length))
        (sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1))) forestT)
      innerCorr stateS.nextFresh (natListGetAt stateS.openWires atom.leftContext.length)
      probeLeft probeRight
    rw [fixNf] at outerCorr
    exact outerCorr
  · exact componentsCorr probeLeft probeRight

/-- ★ **The loop counts stay equal through one arc step** — the partition-keyed variant of the
rootComm-keyed `stepArcAtom_loopsEq`.  Only the CAP branch touches loops; its guard is the
same-component read at the two wires, which transports by `componentsCorr` at the `sigma`-imaged
wire reads.  No injectivity, no rootComm, no freshness. -/
theorem stepArcAtom_loopsCorr {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (openMap : stateT.openWires = stateS.openWires.map sigma)
    (componentsCorr : ∀ probeLeft probeRight,
      isSameComponent stateT.links (sigma probeLeft) (sigma probeRight)
        = isSameComponent stateS.links probeLeft probeRight)
    (loopsEq : stateT.loops = stateS.loops) :
    (stepArcAtom stateT atom).loops = (stepArcAtom stateS atom).loops := by
  unfold stepArcAtom
  split
  · exact loopsEq
  · have guardCorr : isSameComponent stateT.links
          (natListGetAt stateT.openWires atom.leftContext.length)
          (natListGetAt stateT.openWires (atom.leftContext.length + 1))
        = isSameComponent stateS.links
          (natListGetAt stateS.openWires atom.leftContext.length)
          (natListGetAt stateS.openWires (atom.leftContext.length + 1)) := by
      rw [openMap, natListGetAt_map sigma sigmaFixesZero, natListGetAt_map sigma sigmaFixesZero]
      exact componentsCorr (natListGetAt stateS.openWires atom.leftContext.length)
        (natListGetAt stateS.openWires (atom.leftContext.length + 1))
    show (if isSameComponent stateT.links
            (natListGetAt stateT.openWires atom.leftContext.length)
            (natListGetAt stateT.openWires (atom.leftContext.length + 1))
          then stateT.loops + 1 else stateT.loops)
       = (if isSameComponent stateS.links
            (natListGetAt stateS.openWires atom.leftContext.length)
            (natListGetAt stateS.openWires (atom.leftContext.length + 1))
          then stateS.loops + 1 else stateS.loops)
    rw [guardCorr, loopsEq]
  · exact loopsEq

/-- The cup's DOUBLE join (legs `base, base + 1`, event `base + 2`) preserves the
`sigma`-conjugated same-component correspondence, generically over the link lists — the reusable
form of the cup arm of `stepArcAtom_componentsCorr`. -/
theorem isSameComponent_cupJoins_corr (sigma : Nat → Nat)
    (linksS linksT : List (Nat × Nat))
    (forestS : isUnionFindForest linksS) (forestT : isUnionFindForest linksT)
    (freshBase : Nat)
    (fixBase : sigma freshBase = freshBase)
    (fixBaseOne : sigma (freshBase + 1) = freshBase + 1)
    (fixBaseTwo : sigma (freshBase + 2) = freshBase + 2)
    (componentsCorr : ∀ probeLeft probeRight,
      isSameComponent linksT (sigma probeLeft) (sigma probeRight)
        = isSameComponent linksS probeLeft probeRight) :
    ∀ probeLeft probeRight,
      isSameComponent
          (unionFindJoin (unionFindJoin linksT freshBase (freshBase + 1))
            (freshBase + 2) freshBase) (sigma probeLeft) (sigma probeRight)
        = isSameComponent
            (unionFindJoin (unionFindJoin linksS freshBase (freshBase + 1))
              (freshBase + 2) freshBase) probeLeft probeRight := by
  intro probeLeft probeRight
  have innerCorr : ∀ queryLeft queryRight,
      isSameComponent (unionFindJoin linksT freshBase (freshBase + 1))
          (sigma queryLeft) (sigma queryRight)
        = isSameComponent (unionFindJoin linksS freshBase (freshBase + 1))
            queryLeft queryRight := by
    intro queryLeft queryRight
    have twisted := isSameComponent_unionFindJoin_sigmaCorr sigma linksS linksT forestS forestT
      componentsCorr freshBase (freshBase + 1) queryLeft queryRight
    rw [fixBase, fixBaseOne] at twisted
    exact twisted
  have outerCorr := isSameComponent_unionFindJoin_sigmaCorr sigma
    (unionFindJoin linksS freshBase (freshBase + 1))
    (unionFindJoin linksT freshBase (freshBase + 1))
    (isUnionFindForest_unionFindJoin linksS freshBase (freshBase + 1) forestS)
    (isUnionFindForest_unionFindJoin linksT freshBase (freshBase + 1) forestT)
    innerCorr (freshBase + 2) freshBase probeLeft probeRight
  rw [fixBaseTwo, fixBase] at outerCorr
  exact outerCorr

/-- The cup's double join preserves the per-probe PORT-ROOTED count correspondence — two
`countEventsInRoot_unionFindJoin_partitionMatch` applications threaded through the fresh legs. -/
theorem countEventsInRoot_cupJoins_partitionMatch (sigma : Nat → Nat)
    (linksS linksT : List (Nat × Nat))
    (forestS : isUnionFindForest linksS) (forestT : isUnionFindForest linksT)
    (freshBase : Nat)
    (fixBase : sigma freshBase = freshBase)
    (fixBaseOne : sigma (freshBase + 1) = freshBase + 1)
    (fixBaseTwo : sigma (freshBase + 2) = freshBase + 2)
    (componentsCorr : ∀ probeLeft probeRight,
      isSameComponent linksT (sigma probeLeft) (sigma probeRight)
        = isSameComponent linksS probeLeft probeRight)
    (eventsS eventsT : List Nat)
    (countCorr : ∀ probe,
      countEventsInRoot linksT (unionFindRootOf linksT (sigma probe)) eventsT
        = countEventsInRoot linksS (unionFindRootOf linksS probe) eventsS) :
    ∀ probe,
      countEventsInRoot
          (unionFindJoin (unionFindJoin linksT freshBase (freshBase + 1))
            (freshBase + 2) freshBase)
          (unionFindRootOf
            (unionFindJoin (unionFindJoin linksT freshBase (freshBase + 1))
              (freshBase + 2) freshBase) (sigma probe)) eventsT
        = countEventsInRoot
            (unionFindJoin (unionFindJoin linksS freshBase (freshBase + 1))
              (freshBase + 2) freshBase)
            (unionFindRootOf
              (unionFindJoin (unionFindJoin linksS freshBase (freshBase + 1))
                (freshBase + 2) freshBase) probe) eventsS := by
  have innerCorr : ∀ queryLeft queryRight,
      isSameComponent (unionFindJoin linksT freshBase (freshBase + 1))
          (sigma queryLeft) (sigma queryRight)
        = isSameComponent (unionFindJoin linksS freshBase (freshBase + 1))
            queryLeft queryRight := by
    intro queryLeft queryRight
    have twisted := isSameComponent_unionFindJoin_sigmaCorr sigma linksS linksT forestS forestT
      componentsCorr freshBase (freshBase + 1) queryLeft queryRight
    rw [fixBase, fixBaseOne] at twisted
    exact twisted
  have countOne := countEventsInRoot_unionFindJoin_partitionMatch sigma linksS linksT
    forestS forestT freshBase (freshBase + 1) componentsCorr eventsS eventsT countCorr
  rw [fixBase, fixBaseOne] at countOne
  have countTwo := countEventsInRoot_unionFindJoin_partitionMatch sigma
    (unionFindJoin linksS freshBase (freshBase + 1))
    (unionFindJoin linksT freshBase (freshBase + 1))
    (isUnionFindForest_unionFindJoin linksS freshBase (freshBase + 1) forestS)
    (isUnionFindForest_unionFindJoin linksT freshBase (freshBase + 1) forestT)
    (freshBase + 2) freshBase innerCorr eventsS eventsT countOne
  rw [fixBaseTwo, fixBase] at countTwo
  exact countTwo

/-- The cap's double join (merge at the two `sigma`-imaged nodes, event `freshEvent`) preserves
the `sigma`-conjugated same-component correspondence — the reusable form of the cap arm of
`stepArcAtom_componentsCorr`, generic over the two merged nodes. -/
theorem isSameComponent_capJoins_corr (sigma : Nat → Nat)
    (linksS linksT : List (Nat × Nat))
    (forestS : isUnionFindForest linksS) (forestT : isUnionFindForest linksT)
    (freshEvent : Nat) (fixEvent : sigma freshEvent = freshEvent)
    (leftNode rightNode : Nat)
    (componentsCorr : ∀ probeLeft probeRight,
      isSameComponent linksT (sigma probeLeft) (sigma probeRight)
        = isSameComponent linksS probeLeft probeRight) :
    ∀ probeLeft probeRight,
      isSameComponent
          (unionFindJoin (unionFindJoin linksT (sigma leftNode) (sigma rightNode))
            freshEvent (sigma leftNode)) (sigma probeLeft) (sigma probeRight)
        = isSameComponent
            (unionFindJoin (unionFindJoin linksS leftNode rightNode) freshEvent leftNode)
            probeLeft probeRight := by
  intro probeLeft probeRight
  have innerCorr : ∀ queryLeft queryRight,
      isSameComponent (unionFindJoin linksT (sigma leftNode) (sigma rightNode))
          (sigma queryLeft) (sigma queryRight)
        = isSameComponent (unionFindJoin linksS leftNode rightNode) queryLeft queryRight :=
    fun queryLeft queryRight =>
      isSameComponent_unionFindJoin_sigmaCorr sigma linksS linksT forestS forestT
        componentsCorr leftNode rightNode queryLeft queryRight
  have outerCorr := isSameComponent_unionFindJoin_sigmaCorr sigma
    (unionFindJoin linksS leftNode rightNode)
    (unionFindJoin linksT (sigma leftNode) (sigma rightNode))
    (isUnionFindForest_unionFindJoin linksS leftNode rightNode forestS)
    (isUnionFindForest_unionFindJoin linksT (sigma leftNode) (sigma rightNode) forestT)
    innerCorr freshEvent leftNode probeLeft probeRight
  rw [fixEvent] at outerCorr
  exact outerCorr

/-- The cap's double join preserves the per-probe PORT-ROOTED count correspondence — the cap
MERGE redistribution at the partition level, generic over the two merged nodes. -/
theorem countEventsInRoot_capJoins_partitionMatch (sigma : Nat → Nat)
    (linksS linksT : List (Nat × Nat))
    (forestS : isUnionFindForest linksS) (forestT : isUnionFindForest linksT)
    (freshEvent : Nat) (fixEvent : sigma freshEvent = freshEvent)
    (leftNode rightNode : Nat)
    (componentsCorr : ∀ probeLeft probeRight,
      isSameComponent linksT (sigma probeLeft) (sigma probeRight)
        = isSameComponent linksS probeLeft probeRight)
    (eventsS eventsT : List Nat)
    (countCorr : ∀ probe,
      countEventsInRoot linksT (unionFindRootOf linksT (sigma probe)) eventsT
        = countEventsInRoot linksS (unionFindRootOf linksS probe) eventsS) :
    ∀ probe,
      countEventsInRoot
          (unionFindJoin (unionFindJoin linksT (sigma leftNode) (sigma rightNode))
            freshEvent (sigma leftNode))
          (unionFindRootOf
            (unionFindJoin (unionFindJoin linksT (sigma leftNode) (sigma rightNode))
              freshEvent (sigma leftNode)) (sigma probe)) eventsT
        = countEventsInRoot
            (unionFindJoin (unionFindJoin linksS leftNode rightNode) freshEvent leftNode)
            (unionFindRootOf
              (unionFindJoin (unionFindJoin linksS leftNode rightNode) freshEvent leftNode)
              probe) eventsS := by
  have innerCorr : ∀ queryLeft queryRight,
      isSameComponent (unionFindJoin linksT (sigma leftNode) (sigma rightNode))
          (sigma queryLeft) (sigma queryRight)
        = isSameComponent (unionFindJoin linksS leftNode rightNode) queryLeft queryRight :=
    fun queryLeft queryRight =>
      isSameComponent_unionFindJoin_sigmaCorr sigma linksS linksT forestS forestT
        componentsCorr leftNode rightNode queryLeft queryRight
  have countOne := countEventsInRoot_unionFindJoin_partitionMatch sigma linksS linksT
    forestS forestT leftNode rightNode componentsCorr eventsS eventsT countCorr
  have countTwo := countEventsInRoot_unionFindJoin_partitionMatch sigma
    (unionFindJoin linksS leftNode rightNode)
    (unionFindJoin linksT (sigma leftNode) (sigma rightNode))
    (isUnionFindForest_unionFindJoin linksS leftNode rightNode forestS)
    (isUnionFindForest_unionFindJoin linksT (sigma leftNode) (sigma rightNode) forestT)
    freshEvent leftNode innerCorr eventsS eventsT countOne
  rw [fixEvent] at countTwo
  exact countTwo

/-- ★ **The per-probe CUP-event count correspondence survives one arc step.**  CUP: the new
event (`nf + 2`, shared by both sides) contributes the same-component boolean at the probe —
transported by `isSameComponent_cupJoins_corr` — and the old events transport by
`countEventsInRoot_cupJoins_partitionMatch`; CAP: the cup-event list is untouched, so the cap
joins transport the counts outright; BOX: nothing changes.  Freshness-free. -/
theorem stepArcAtom_cupCountCorr {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (forestS : isUnionFindForest stateS.links) (forestT : isUnionFindForest stateT.links)
    (nfEq : stateS.nextFresh = stateT.nextFresh)
    (openMap : stateT.openWires = stateS.openWires.map sigma)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (componentsCorr : ∀ probeLeft probeRight,
      isSameComponent stateT.links (sigma probeLeft) (sigma probeRight)
        = isSameComponent stateS.links probeLeft probeRight)
    (cupCountCorr : ∀ probe,
      countEventsInRoot stateT.links (unionFindRootOf stateT.links (sigma probe))
          stateT.cupEventNodes
        = countEventsInRoot stateS.links (unionFindRootOf stateS.links probe)
            stateS.cupEventNodes) :
    ∀ probe,
      countEventsInRoot (stepArcAtom stateT atom).links
          (unionFindRootOf (stepArcAtom stateT atom).links (sigma probe))
          (stepArcAtom stateT atom).cupEventNodes
        = countEventsInRoot (stepArcAtom stateS atom).links
            (unionFindRootOf (stepArcAtom stateS atom).links probe)
            (stepArcAtom stateS atom).cupEventNodes := by
  intro probe
  have fixNf : sigma stateS.nextFresh = stateS.nextFresh :=
    fixesAbove stateS.nextFresh (Nat.le_refl _)
  have fixNfOne : sigma (stateS.nextFresh + 1) = stateS.nextFresh + 1 :=
    fixesAbove (stateS.nextFresh + 1) (Nat.le_add_right _ _)
  have fixNfTwo : sigma (stateS.nextFresh + 2) = stateS.nextFresh + 2 :=
    fixesAbove (stateS.nextFresh + 2) (Nat.le_add_right _ _)
  unfold stepArcAtom
  split
  · show countEventsInRoot
        (unionFindJoin (unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1))
          (stateT.nextFresh + 2) stateT.nextFresh)
        (unionFindRootOf
          (unionFindJoin (unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1))
            (stateT.nextFresh + 2) stateT.nextFresh) (sigma probe))
        ((stateT.nextFresh + 2) :: stateT.cupEventNodes)
      = countEventsInRoot
          (unionFindJoin (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
            (stateS.nextFresh + 2) stateS.nextFresh)
          (unionFindRootOf
            (unionFindJoin (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
              (stateS.nextFresh + 2) stateS.nextFresh) probe)
          ((stateS.nextFresh + 2) :: stateS.cupEventNodes)
    rw [← nfEq]
    have componentsAfter := isSameComponent_cupJoins_corr sigma stateS.links stateT.links
      forestS forestT stateS.nextFresh fixNf fixNfOne fixNfTwo componentsCorr
    have countTail := countEventsInRoot_cupJoins_partitionMatch sigma stateS.links stateT.links
      forestS forestT stateS.nextFresh fixNf fixNfOne fixNfTwo componentsCorr
      stateS.cupEventNodes stateT.cupEventNodes cupCountCorr
    have headCorr : (unionFindRootOf
          (unionFindJoin (unionFindJoin stateT.links stateS.nextFresh (stateS.nextFresh + 1))
            (stateS.nextFresh + 2) stateS.nextFresh) (stateS.nextFresh + 2)
          == unionFindRootOf
            (unionFindJoin (unionFindJoin stateT.links stateS.nextFresh (stateS.nextFresh + 1))
              (stateS.nextFresh + 2) stateS.nextFresh) (sigma probe))
        = (unionFindRootOf
            (unionFindJoin (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
              (stateS.nextFresh + 2) stateS.nextFresh) (stateS.nextFresh + 2)
            == unionFindRootOf
              (unionFindJoin (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
                (stateS.nextFresh + 2) stateS.nextFresh) probe) := by
      have fromAfter := componentsAfter (stateS.nextFresh + 2) probe
      rw [fixNfTwo] at fromAfter
      exact fromAfter
    show (if unionFindRootOf
            (unionFindJoin (unionFindJoin stateT.links stateS.nextFresh (stateS.nextFresh + 1))
              (stateS.nextFresh + 2) stateS.nextFresh) (stateS.nextFresh + 2)
            == unionFindRootOf
              (unionFindJoin (unionFindJoin stateT.links stateS.nextFresh (stateS.nextFresh + 1))
                (stateS.nextFresh + 2) stateS.nextFresh) (sigma probe)
          then (1 : Nat) else 0)
        + countEventsInRoot
            (unionFindJoin (unionFindJoin stateT.links stateS.nextFresh (stateS.nextFresh + 1))
              (stateS.nextFresh + 2) stateS.nextFresh)
            (unionFindRootOf
              (unionFindJoin (unionFindJoin stateT.links stateS.nextFresh (stateS.nextFresh + 1))
                (stateS.nextFresh + 2) stateS.nextFresh) (sigma probe)) stateT.cupEventNodes
      = (if unionFindRootOf
            (unionFindJoin (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
              (stateS.nextFresh + 2) stateS.nextFresh) (stateS.nextFresh + 2)
            == unionFindRootOf
              (unionFindJoin (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
                (stateS.nextFresh + 2) stateS.nextFresh) probe
          then (1 : Nat) else 0)
        + countEventsInRoot
            (unionFindJoin (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
              (stateS.nextFresh + 2) stateS.nextFresh)
            (unionFindRootOf
              (unionFindJoin (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
                (stateS.nextFresh + 2) stateS.nextFresh) probe) stateS.cupEventNodes
    rw [headCorr, countTail probe]
  · have wireLeft : natListGetAt stateT.openWires atom.leftContext.length
        = sigma (natListGetAt stateS.openWires atom.leftContext.length) := by
      rw [openMap, natListGetAt_map sigma sigmaFixesZero]
    have wireRight : natListGetAt stateT.openWires (atom.leftContext.length + 1)
        = sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1)) := by
      rw [openMap, natListGetAt_map sigma sigmaFixesZero]
    show countEventsInRoot
        (unionFindJoin (unionFindJoin stateT.links
            (natListGetAt stateT.openWires atom.leftContext.length)
            (natListGetAt stateT.openWires (atom.leftContext.length + 1)))
          stateT.nextFresh (natListGetAt stateT.openWires atom.leftContext.length))
        (unionFindRootOf
          (unionFindJoin (unionFindJoin stateT.links
              (natListGetAt stateT.openWires atom.leftContext.length)
              (natListGetAt stateT.openWires (atom.leftContext.length + 1)))
            stateT.nextFresh (natListGetAt stateT.openWires atom.leftContext.length))
          (sigma probe)) stateT.cupEventNodes
      = countEventsInRoot
          (unionFindJoin (unionFindJoin stateS.links
              (natListGetAt stateS.openWires atom.leftContext.length)
              (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
            stateS.nextFresh (natListGetAt stateS.openWires atom.leftContext.length))
          (unionFindRootOf
            (unionFindJoin (unionFindJoin stateS.links
                (natListGetAt stateS.openWires atom.leftContext.length)
                (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
              stateS.nextFresh (natListGetAt stateS.openWires atom.leftContext.length))
            probe) stateS.cupEventNodes
    rw [← nfEq, wireLeft, wireRight]
    exact countEventsInRoot_capJoins_partitionMatch sigma stateS.links stateT.links
      forestS forestT stateS.nextFresh fixNf
      (natListGetAt stateS.openWires atom.leftContext.length)
      (natListGetAt stateS.openWires (atom.leftContext.length + 1))
      componentsCorr stateS.cupEventNodes stateT.cupEventNodes cupCountCorr probe
  · exact cupCountCorr probe

/-- ★ **The per-probe CAP-event count correspondence survives one arc step.**  Mirror of
`stepArcAtom_cupCountCorr`: the CUP arm leaves the cap-event list untouched (cup joins
transport the counts outright), the CAP arm conses the shared fresh event node (head via
`isSameComponent_capJoins_corr`, tail via `countEventsInRoot_capJoins_partitionMatch`). -/
theorem stepArcAtom_capCountCorr {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (forestS : isUnionFindForest stateS.links) (forestT : isUnionFindForest stateT.links)
    (nfEq : stateS.nextFresh = stateT.nextFresh)
    (openMap : stateT.openWires = stateS.openWires.map sigma)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (componentsCorr : ∀ probeLeft probeRight,
      isSameComponent stateT.links (sigma probeLeft) (sigma probeRight)
        = isSameComponent stateS.links probeLeft probeRight)
    (capCountCorr : ∀ probe,
      countEventsInRoot stateT.links (unionFindRootOf stateT.links (sigma probe))
          stateT.capEventNodes
        = countEventsInRoot stateS.links (unionFindRootOf stateS.links probe)
            stateS.capEventNodes) :
    ∀ probe,
      countEventsInRoot (stepArcAtom stateT atom).links
          (unionFindRootOf (stepArcAtom stateT atom).links (sigma probe))
          (stepArcAtom stateT atom).capEventNodes
        = countEventsInRoot (stepArcAtom stateS atom).links
            (unionFindRootOf (stepArcAtom stateS atom).links probe)
            (stepArcAtom stateS atom).capEventNodes := by
  intro probe
  have fixNf : sigma stateS.nextFresh = stateS.nextFresh :=
    fixesAbove stateS.nextFresh (Nat.le_refl _)
  have fixNfOne : sigma (stateS.nextFresh + 1) = stateS.nextFresh + 1 :=
    fixesAbove (stateS.nextFresh + 1) (Nat.le_add_right _ _)
  have fixNfTwo : sigma (stateS.nextFresh + 2) = stateS.nextFresh + 2 :=
    fixesAbove (stateS.nextFresh + 2) (Nat.le_add_right _ _)
  unfold stepArcAtom
  split
  · show countEventsInRoot
        (unionFindJoin (unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1))
          (stateT.nextFresh + 2) stateT.nextFresh)
        (unionFindRootOf
          (unionFindJoin (unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1))
            (stateT.nextFresh + 2) stateT.nextFresh) (sigma probe)) stateT.capEventNodes
      = countEventsInRoot
          (unionFindJoin (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
            (stateS.nextFresh + 2) stateS.nextFresh)
          (unionFindRootOf
            (unionFindJoin (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
              (stateS.nextFresh + 2) stateS.nextFresh) probe) stateS.capEventNodes
    rw [← nfEq]
    exact countEventsInRoot_cupJoins_partitionMatch sigma stateS.links stateT.links
      forestS forestT stateS.nextFresh fixNf fixNfOne fixNfTwo componentsCorr
      stateS.capEventNodes stateT.capEventNodes capCountCorr probe
  · have wireLeft : natListGetAt stateT.openWires atom.leftContext.length
        = sigma (natListGetAt stateS.openWires atom.leftContext.length) := by
      rw [openMap, natListGetAt_map sigma sigmaFixesZero]
    have wireRight : natListGetAt stateT.openWires (atom.leftContext.length + 1)
        = sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1)) := by
      rw [openMap, natListGetAt_map sigma sigmaFixesZero]
    show countEventsInRoot
        (unionFindJoin (unionFindJoin stateT.links
            (natListGetAt stateT.openWires atom.leftContext.length)
            (natListGetAt stateT.openWires (atom.leftContext.length + 1)))
          stateT.nextFresh (natListGetAt stateT.openWires atom.leftContext.length))
        (unionFindRootOf
          (unionFindJoin (unionFindJoin stateT.links
              (natListGetAt stateT.openWires atom.leftContext.length)
              (natListGetAt stateT.openWires (atom.leftContext.length + 1)))
            stateT.nextFresh (natListGetAt stateT.openWires atom.leftContext.length))
          (sigma probe))
        (stateT.nextFresh :: stateT.capEventNodes)
      = countEventsInRoot
          (unionFindJoin (unionFindJoin stateS.links
              (natListGetAt stateS.openWires atom.leftContext.length)
              (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
            stateS.nextFresh (natListGetAt stateS.openWires atom.leftContext.length))
          (unionFindRootOf
            (unionFindJoin (unionFindJoin stateS.links
                (natListGetAt stateS.openWires atom.leftContext.length)
                (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
              stateS.nextFresh (natListGetAt stateS.openWires atom.leftContext.length))
            probe)
          (stateS.nextFresh :: stateS.capEventNodes)
    rw [← nfEq, wireLeft, wireRight]
    have componentsAfter := isSameComponent_capJoins_corr sigma stateS.links stateT.links
      forestS forestT stateS.nextFresh fixNf
      (natListGetAt stateS.openWires atom.leftContext.length)
      (natListGetAt stateS.openWires (atom.leftContext.length + 1)) componentsCorr
    have countTail := countEventsInRoot_capJoins_partitionMatch sigma stateS.links stateT.links
      forestS forestT stateS.nextFresh fixNf
      (natListGetAt stateS.openWires atom.leftContext.length)
      (natListGetAt stateS.openWires (atom.leftContext.length + 1))
      componentsCorr stateS.capEventNodes stateT.capEventNodes capCountCorr
    have headCorr : (unionFindRootOf
          (unionFindJoin (unionFindJoin stateT.links
              (sigma (natListGetAt stateS.openWires atom.leftContext.length))
              (sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1))))
            stateS.nextFresh (sigma (natListGetAt stateS.openWires atom.leftContext.length)))
          stateS.nextFresh
          == unionFindRootOf
            (unionFindJoin (unionFindJoin stateT.links
                (sigma (natListGetAt stateS.openWires atom.leftContext.length))
                (sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1))))
              stateS.nextFresh (sigma (natListGetAt stateS.openWires atom.leftContext.length)))
            (sigma probe))
        = (unionFindRootOf
            (unionFindJoin (unionFindJoin stateS.links
                (natListGetAt stateS.openWires atom.leftContext.length)
                (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
              stateS.nextFresh (natListGetAt stateS.openWires atom.leftContext.length))
            stateS.nextFresh
            == unionFindRootOf
              (unionFindJoin (unionFindJoin stateS.links
                  (natListGetAt stateS.openWires atom.leftContext.length)
                  (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
                stateS.nextFresh (natListGetAt stateS.openWires atom.leftContext.length))
              probe) := by
      have fromAfter := componentsAfter stateS.nextFresh probe
      rw [fixNf] at fromAfter
      exact fromAfter
    show (if unionFindRootOf
            (unionFindJoin (unionFindJoin stateT.links
                (sigma (natListGetAt stateS.openWires atom.leftContext.length))
                (sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1))))
              stateS.nextFresh (sigma (natListGetAt stateS.openWires atom.leftContext.length)))
            stateS.nextFresh
            == unionFindRootOf
              (unionFindJoin (unionFindJoin stateT.links
                  (sigma (natListGetAt stateS.openWires atom.leftContext.length))
                  (sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1))))
                stateS.nextFresh
                (sigma (natListGetAt stateS.openWires atom.leftContext.length)))
              (sigma probe)
          then (1 : Nat) else 0)
        + countEventsInRoot
            (unionFindJoin (unionFindJoin stateT.links
                (sigma (natListGetAt stateS.openWires atom.leftContext.length))
                (sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1))))
              stateS.nextFresh (sigma (natListGetAt stateS.openWires atom.leftContext.length)))
            (unionFindRootOf
              (unionFindJoin (unionFindJoin stateT.links
                  (sigma (natListGetAt stateS.openWires atom.leftContext.length))
                  (sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1))))
                stateS.nextFresh
                (sigma (natListGetAt stateS.openWires atom.leftContext.length)))
              (sigma probe)) stateT.capEventNodes
      = (if unionFindRootOf
            (unionFindJoin (unionFindJoin stateS.links
                (natListGetAt stateS.openWires atom.leftContext.length)
                (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
              stateS.nextFresh (natListGetAt stateS.openWires atom.leftContext.length))
            stateS.nextFresh
            == unionFindRootOf
              (unionFindJoin (unionFindJoin stateS.links
                  (natListGetAt stateS.openWires atom.leftContext.length)
                  (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
                stateS.nextFresh (natListGetAt stateS.openWires atom.leftContext.length))
              probe
          then (1 : Nat) else 0)
        + countEventsInRoot
            (unionFindJoin (unionFindJoin stateS.links
                (natListGetAt stateS.openWires atom.leftContext.length)
                (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
              stateS.nextFresh (natListGetAt stateS.openWires atom.leftContext.length))
            (unionFindRootOf
              (unionFindJoin (unionFindJoin stateS.links
                  (natListGetAt stateS.openWires atom.leftContext.length)
                  (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
                stateS.nextFresh (natListGetAt stateS.openWires atom.leftContext.length))
              probe) stateS.capEventNodes
    rw [headCorr, countTail probe]
  · exact capCountCorr probe

/-- ★ **`ArcPartitionSim` is STEP-STABLE** — the assembled single-step simulation.  Every field
transports through a common `stepArcAtom`: `openMap`/`nfEq` by the (rootComm-free) W6 lemmas,
`loopsEq`/`componentsCorr` by the gamma2a partition step lemmas, the two count fields by the
partition count step lemmas, forests by `isUnionFindForest_stepArcAtom`.  Hypotheses: only
`sigmaFixesZero` + `fixesAbove` — NO `ArcStateFresh`, NO `0 < nextFresh`, NO injectivity. -/
theorem arcPartitionSim_stepArcAtom {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (sim : ArcPartitionSim sigma stateS stateT) :
    ArcPartitionSim sigma (stepArcAtom stateS atom) (stepArcAtom stateT atom) where
  openMap := stepArcAtom_openWires_map sigma stateS stateT atom sim.openMap sim.nfEq fixesAbove
  nfEq := stepArcAtom_nextFresh_eq stateS stateT atom sim.nfEq
  loopsEq := stepArcAtom_loopsCorr sigma sigmaFixesZero stateS stateT atom sim.openMap
    sim.componentsCorr sim.loopsEq
  componentsCorr := stepArcAtom_componentsCorr sigma sigmaFixesZero stateS stateT atom
    sim.forestS sim.forestT sim.nfEq sim.openMap fixesAbove sim.componentsCorr
  cupCountCorr := stepArcAtom_cupCountCorr sigma sigmaFixesZero stateS stateT atom
    sim.forestS sim.forestT sim.nfEq sim.openMap fixesAbove sim.componentsCorr sim.cupCountCorr
  capCountCorr := stepArcAtom_capCountCorr sigma sigmaFixesZero stateS stateT atom
    sim.forestS sim.forestT sim.nfEq sim.openMap fixesAbove sim.componentsCorr sim.capCountCorr
  forestS := isUnionFindForest_stepArcAtom stateS atom sim.forestS
  forestT := isUnionFindForest_stepArcAtom stateT atom sim.forestT

/-- **Honesty marker — the partition simulation is SINGLE-STEP STABLE.**  The join substrate
(`isSameComponent_unionFindJoin_sigmaCorr`, `countEventsInRoot_unionFindJoin_partitionMatch`),
the generic cup/cap double-join transports, all six per-field step lemmas, and the assembled
`arcPartitionSim_stepArcAtom` — all freshness-free (only `sigmaFixesZero` + `fixesAbove`).
What this marker does NOT claim: the spine/cell FOLDS (threading the shrinking `fixesAbove`
through `processArcSpine` / `runArcCell` — the next brick), and the cap-cap CORE instance
under the event transposition.  `= true` records join substrate + single-step stability. -/
def fxMode_hasPartitionJoinTransport : Bool := true

end FX1Poly.Polygraph
