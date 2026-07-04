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

/-- **Honesty marker — the partition simulation's JOIN substrate is BUILT.**  Both rootComm-free
fields of `ArcPartitionSim` transport through a corresponding `unionFindJoin`:
`isSameComponent_unionFindJoin_sigmaCorr` for `componentsCorr` and
`countEventsInRoot_unionFindJoin_partitionMatch` for the per-probe port-rooted counts.  What
this marker does NOT claim: the `stepArcAtom`-level step lemma (assembling these through the
cup's two fresh joins, the cap's wire-read merge and the event cons — the next brick), the
spine/cell folds, and the cap-cap core instance.  `= true` records the join substrate only. -/
def fxMode_hasPartitionJoinTransport : Bool := true

end FX1Poly.Polygraph
