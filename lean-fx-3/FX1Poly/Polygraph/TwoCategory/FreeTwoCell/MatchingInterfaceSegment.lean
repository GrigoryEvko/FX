import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingInterfaceTransfer
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldRename
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldSupport

/-! # MatchingInterfaceSegment — the segment-transfer discharge (MODE3-D)

The interface-transfer engine runs on an abstract `Corresponds` relation whose one semantic
hypothesis is the SEGMENT TRANSFER: empty-base connectivity of the first renamed trace at
corresponding probes yields empty-base connectivity of the second.  This file discharges that
hypothesis from CANONICAL-level data only:

* `InterfaceCorresponds` — the packaged relation: below-base identifiers self-correspond, and
  `sigma`-images of canonically paired identifiers correspond;
* `segmentTransfers_ofCanonicalPairs` — ★ the discharge.  Each probe splits DECIDABLY on
  membership in the renamed trace's support (`nodeAppearsInJoinEvents`, a Bool scan — no
  classical image test): untouched probes collapse by fold-support rigidity; touched
  below-base probes expose a concrete preimage (a PORT, by the zone bound), which
  self-pairs; paired probes carry their canonical pair.  Every leaf then follows one road:
  rename equivariance down to the canonical fold, the canonical transfer across, rename
  equivariance back up;
* `isSameComponent_applyJoinEvents_transferAcrossInterface_ofCanonicalPairs` — the packaged
  one-directional composite transfer: brick 3's engine instantiated at the discharged
  relation.

The canonical transfer hypothesis (`canonicalTransfers`) is exactly what extract equality of
the two canonical runs provides at boundary positions (bottom ports self-pair positionally,
top wires pair positionally) — that instantiation is the NEXT brick.  Raw Lean 4 + Init;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (Bool scans and Nat/Bool kits — core lemmas leak propext) -/

/-- Does the node appear as an endpoint of any trace event?  A Bool scan — the decidable
support test the rigidity split runs on. -/
private def nodeAppearsInJoinEvents : List (Nat × Nat) → Nat → Bool
  | [], _ => false
  | event :: restEvents, node =>
      (event.1 == node) || ((event.2 == node) || nodeAppearsInJoinEvents restEvents node)

private theorem natBeqSelf (node : Nat) : (node == node) = true :=
  decide_eq_true rfl

private theorem natEqOfBeq (leftNat rightNat : Nat)
    (beqTrue : (leftNat == rightNat) = true) : leftNat = rightNat :=
  of_decide_eq_true beqTrue

private theorem boolOrEqTrue_ofLeft (leftFlag rightFlag : Bool)
    (leftTrue : leftFlag = true) : (leftFlag || rightFlag) = true := by
  rw [leftTrue]
  rfl

private theorem boolOrEqTrue_ofRight (leftFlag rightFlag : Bool)
    (rightTrue : rightFlag = true) : (leftFlag || rightFlag) = true := by
  cases leftFlag with
  | true => rfl
  | false => exact rightTrue

/-- Every event endpoint appears in the trace's support scan — the closure form the rigidity
lemmas consume. -/
private theorem nodeAppears_ofMem : (events : List (Nat × Nat)) → (pair : Nat × Nat) →
    pair ∈ events →
    nodeAppearsInJoinEvents events pair.1 = true
      ∧ nodeAppearsInJoinEvents events pair.2 = true := by
  intro events
  induction events with
  | nil =>
      intro pair absurdMembership
      cases absurdMembership
  | cons headEvent restEvents restAppears =>
      intro pair membership
      cases membership with
      | head =>
          exact ⟨boolOrEqTrue_ofLeft _ _ (natBeqSelf headEvent.1),
            boolOrEqTrue_ofRight _ _ (boolOrEqTrue_ofLeft _ _ (natBeqSelf headEvent.2))⟩
      | tail _ restMembership =>
          have restBoth := restAppears pair restMembership
          exact ⟨boolOrEqTrue_ofRight _ _ (boolOrEqTrue_ofRight _ _ restBoth.1),
            boolOrEqTrue_ofRight _ _ (boolOrEqTrue_ofRight _ _ restBoth.2)⟩

/-- A node in the RENAMED trace's support has a concrete `sigma`-preimage — constructive
extraction from the scan, no image existential needed. -/
private theorem renamedAppearsPreimage (sigma : Nat → Nat) :
    (events : List (Nat × Nat)) → (node : Nat) →
    nodeAppearsInJoinEvents (events.map (fun event => (sigma event.1, sigma event.2))) node
      = true →
    ∃ preimage : Nat, sigma preimage = node := by
  intro events
  induction events with
  | nil =>
      intro node appears
      exact Bool.noConfusion appears
  | cons headEvent restEvents restPreimage =>
      intro node appears
      have appearsShape : ((sigma headEvent.1 == node)
          || ((sigma headEvent.2 == node)
            || nodeAppearsInJoinEvents
                (restEvents.map (fun event => (sigma event.1, sigma event.2))) node)) = true :=
        appears
      cases firstBeq : (sigma headEvent.1 == node) with
      | true => exact ⟨headEvent.1, natEqOfBeq _ _ firstBeq⟩
      | false =>
          rw [firstBeq] at appearsShape
          cases secondBeq : (sigma headEvent.2 == node) with
          | true => exact ⟨headEvent.2, natEqOfBeq _ _ secondBeq⟩
          | false =>
              rw [secondBeq] at appearsShape
              exact restPreimage node appearsShape

/-! ## The packaged correspondence -/

/-- The **interface correspondence** between the two composites' identifiers: below-base
identifiers self-correspond (mid ports and gamma-interior wires — both composites share the
mid state), and `sigma`-images of canonically paired identifiers correspond (the boundary
transport). -/
def InterfaceCorresponds (sigma : Nat → Nat) (freshBase : Nat)
    (CanonicalPair : Nat → Nat → Prop) (node image : Nat) : Prop :=
  (node < freshBase ∧ node = image)
    ∨ (∃ nodeCanonicalA nodeCanonicalB : Nat, CanonicalPair nodeCanonicalA nodeCanonicalB
        ∧ node = sigma nodeCanonicalA ∧ image = sigma nodeCanonicalB)

/-- Below-base identifiers self-correspond — the engine's `belowBaseCorresponds` field. -/
theorem interfaceCorresponds_ofBelowBase (sigma : Nat → Nat) (freshBase : Nat)
    (CanonicalPair : Nat → Nat → Prop) (node : Nat) (nodeBelow : node < freshBase) :
    InterfaceCorresponds sigma freshBase CanonicalPair node node :=
  Or.inl ⟨nodeBelow, rfl⟩

/-- `sigma`-images of a canonical pair correspond — the boundary-transport constructor. -/
theorem interfaceCorresponds_ofCanonicalPair (sigma : Nat → Nat) (freshBase : Nat)
    (CanonicalPair : Nat → Nat → Prop) (nodeCanonicalA nodeCanonicalB : Nat)
    (paired : CanonicalPair nodeCanonicalA nodeCanonicalB) :
    InterfaceCorresponds sigma freshBase CanonicalPair
      (sigma nodeCanonicalA) (sigma nodeCanonicalB) :=
  Or.inr ⟨nodeCanonicalA, nodeCanonicalB, paired, rfl, rfl⟩

/-! ## The segment-transfer discharge -/

/-- ★ **The segment transfer discharges from canonical data.**  Given an injective rename,
below-base ports self-pairing canonically, and the canonical transfer (paired canonical
probes carry empty-base connectivity from trace A to trace B), the renamed traces' empty-base
folds correspond at `InterfaceCorresponds`-related probes.  Probes split decidably on the
renamed trace's support: untouched probes collapse by rigidity, touched below-base probes
expose a port preimage which self-pairs, and every leaf runs rename equivariance down,
the canonical transfer across, and rename equivariance back up. -/
theorem segmentTransfers_ofCanonicalPairs (sigma : Nat → Nat)
    (isInjective : ∀ idOne idTwo : Nat, sigma idOne = sigma idTwo → idOne = idTwo)
    (freshBase : Nat) (CanonicalPair : Nat → Nat → Prop)
    (eventsA eventsB : List (Nat × Nat))
    (portPairsSelf : ∀ preimage : Nat, sigma preimage < freshBase →
      CanonicalPair preimage preimage)
    (canonicalTransfers : ∀ pivotCanonicalA pivotCanonicalB
        probeCanonicalA probeCanonicalB : Nat,
      CanonicalPair pivotCanonicalA pivotCanonicalB →
      CanonicalPair probeCanonicalA probeCanonicalB →
      isSameComponent (applyJoinEvents eventsA []) pivotCanonicalA probeCanonicalA = true →
      isSameComponent (applyJoinEvents eventsB []) pivotCanonicalB probeCanonicalB = true)
    (pivotNode probeNode pivotImage probeImage : Nat)
    (pivotCorresponds : InterfaceCorresponds sigma freshBase CanonicalPair
      pivotNode pivotImage)
    (probeCorresponds : InterfaceCorresponds sigma freshBase CanonicalPair
      probeNode probeImage)
    (segmentConnected : isSameComponent
      (applyJoinEvents (eventsA.map (fun event => (sigma event.1, sigma event.2))) [])
      pivotNode probeNode = true) :
    isSameComponent
      (applyJoinEvents (eventsB.map (fun event => (sigma event.1, sigma event.2))) [])
      pivotImage probeImage = true := by
  have renamedClosed : ∀ pair ∈ eventsA.map (fun event => (sigma event.1, sigma event.2)),
      (nodeAppearsInJoinEvents
          (eventsA.map (fun event => (sigma event.1, sigma event.2))) pair.1 = true)
        ∧ (nodeAppearsInJoinEvents
          (eventsA.map (fun event => (sigma event.1, sigma event.2))) pair.2 = true) :=
    fun pair pairListed =>
      nodeAppears_ofMem (eventsA.map (fun event => (sigma event.1, sigma event.2)))
        pair pairListed
  cases pivotCorresponds with
  | inl pivotSelf =>
      obtain ⟨pivotBelow, pivotSelfEq⟩ := pivotSelf
      cases pivotAppears : nodeAppearsInJoinEvents
          (eventsA.map (fun event => (sigma event.1, sigma event.2))) pivotNode with
      | false =>
          have nodesEq : pivotNode = probeNode :=
            nodesEqual_ofUntouchedFoldConnected
              (fun candidate => nodeAppearsInJoinEvents
                (eventsA.map (fun event => (sigma event.1, sigma event.2))) candidate = true)
              (eventsA.map (fun event => (sigma event.1, sigma event.2))) renamedClosed
              pivotNode probeNode
              (fun touched => Bool.noConfusion (pivotAppears.symm.trans touched))
              segmentConnected
          cases probeCorresponds with
          | inl probeSelf =>
              obtain ⟨_, probeSelfEq⟩ := probeSelf
              rw [← pivotSelfEq, ← probeSelfEq, nodesEq]
              exact isSameComponent_self _ probeNode
          | inr probePaired =>
              obtain ⟨probeCanonicalA, probeCanonicalB, probePair,
                probeNodeEq, probeImageEq⟩ := probePaired
              have sigmaProbeBelow : sigma probeCanonicalA < freshBase := by
                rw [← probeNodeEq, ← nodesEq]
                exact pivotBelow
              have transferred : isSameComponent (applyJoinEvents eventsB [])
                  probeCanonicalA probeCanonicalB = true :=
                canonicalTransfers probeCanonicalA probeCanonicalA
                  probeCanonicalA probeCanonicalB
                  (portPairsSelf probeCanonicalA sigmaProbeBelow) probePair
                  (isSameComponent_self (applyJoinEvents eventsA []) probeCanonicalA)
              rw [← pivotSelfEq, nodesEq, probeNodeEq, probeImageEq,
                componentView_applyJoinEvents_ofRename sigma isInjective eventsB
                  probeCanonicalA probeCanonicalB]
              exact transferred
      | true =>
          obtain ⟨pivotPre, pivotPreMaps⟩ :=
            renamedAppearsPreimage sigma eventsA pivotNode pivotAppears
          have sigmaPivotBelow : sigma pivotPre < freshBase := by
            rw [pivotPreMaps]
            exact pivotBelow
          have pivotSelfPair : CanonicalPair pivotPre pivotPre :=
            portPairsSelf pivotPre sigmaPivotBelow
          cases probeCorresponds with
          | inl probeSelf =>
              obtain ⟨probeBelow, probeSelfEq⟩ := probeSelf
              cases probeAppears : nodeAppearsInJoinEvents
                  (eventsA.map (fun event => (sigma event.1, sigma event.2))) probeNode with
              | false =>
                  have nodesEq : pivotNode = probeNode :=
                    nodesEqual_ofFoldConnectedToUntouched
                      (fun candidate => nodeAppearsInJoinEvents
                        (eventsA.map (fun event => (sigma event.1, sigma event.2)))
                        candidate = true)
                      (eventsA.map (fun event => (sigma event.1, sigma event.2)))
                      renamedClosed pivotNode probeNode
                      (fun touched => Bool.noConfusion (probeAppears.symm.trans touched))
                      segmentConnected
                  rw [← pivotSelfEq, ← probeSelfEq, nodesEq]
                  exact isSameComponent_self _ probeNode
              | true =>
                  obtain ⟨probePre, probePreMaps⟩ :=
                    renamedAppearsPreimage sigma eventsA probeNode probeAppears
                  have sigmaProbeBelow : sigma probePre < freshBase := by
                    rw [probePreMaps]
                    exact probeBelow
                  have canonicalConnectedA : isSameComponent (applyJoinEvents eventsA [])
                      pivotPre probePre = true := by
                    rw [← componentView_applyJoinEvents_ofRename sigma isInjective eventsA
                      pivotPre probePre, pivotPreMaps, probePreMaps]
                    exact segmentConnected
                  have transferred : isSameComponent (applyJoinEvents eventsB [])
                      pivotPre probePre = true :=
                    canonicalTransfers pivotPre pivotPre probePre probePre
                      pivotSelfPair (portPairsSelf probePre sigmaProbeBelow)
                      canonicalConnectedA
                  rw [← pivotSelfEq, ← probeSelfEq, ← pivotPreMaps, ← probePreMaps,
                    componentView_applyJoinEvents_ofRename sigma isInjective eventsB
                      pivotPre probePre]
                  exact transferred
          | inr probePaired =>
              obtain ⟨probeCanonicalA, probeCanonicalB, probePair,
                probeNodeEq, probeImageEq⟩ := probePaired
              have canonicalConnectedA : isSameComponent (applyJoinEvents eventsA [])
                  pivotPre probeCanonicalA = true := by
                rw [← componentView_applyJoinEvents_ofRename sigma isInjective eventsA
                  pivotPre probeCanonicalA, pivotPreMaps, ← probeNodeEq]
                exact segmentConnected
              have transferred : isSameComponent (applyJoinEvents eventsB [])
                  pivotPre probeCanonicalB = true :=
                canonicalTransfers pivotPre pivotPre probeCanonicalA probeCanonicalB
                  pivotSelfPair probePair canonicalConnectedA
              rw [← pivotSelfEq, ← pivotPreMaps, probeImageEq,
                componentView_applyJoinEvents_ofRename sigma isInjective eventsB
                  pivotPre probeCanonicalB]
              exact transferred
  | inr pivotPaired =>
      obtain ⟨pivotCanonicalA, pivotCanonicalB, pivotPair,
        pivotNodeEq, pivotImageEq⟩ := pivotPaired
      cases probeCorresponds with
      | inl probeSelf =>
          obtain ⟨probeBelow, probeSelfEq⟩ := probeSelf
          cases probeAppears : nodeAppearsInJoinEvents
              (eventsA.map (fun event => (sigma event.1, sigma event.2))) probeNode with
          | false =>
              have nodesEq : pivotNode = probeNode :=
                nodesEqual_ofFoldConnectedToUntouched
                  (fun candidate => nodeAppearsInJoinEvents
                    (eventsA.map (fun event => (sigma event.1, sigma event.2)))
                    candidate = true)
                  (eventsA.map (fun event => (sigma event.1, sigma event.2)))
                  renamedClosed pivotNode probeNode
                  (fun touched => Bool.noConfusion (probeAppears.symm.trans touched))
                  segmentConnected
              have sigmaPivotBelow : sigma pivotCanonicalA < freshBase := by
                rw [← pivotNodeEq, nodesEq]
                exact probeBelow
              have transferred : isSameComponent (applyJoinEvents eventsB [])
                  pivotCanonicalB pivotCanonicalA = true :=
                canonicalTransfers pivotCanonicalA pivotCanonicalB
                  pivotCanonicalA pivotCanonicalA pivotPair
                  (portPairsSelf pivotCanonicalA sigmaPivotBelow)
                  (isSameComponent_self (applyJoinEvents eventsA []) pivotCanonicalA)
              rw [pivotImageEq, ← probeSelfEq, ← nodesEq, pivotNodeEq,
                componentView_applyJoinEvents_ofRename sigma isInjective eventsB
                  pivotCanonicalB pivotCanonicalA]
              exact transferred
          | true =>
              obtain ⟨probePre, probePreMaps⟩ :=
                renamedAppearsPreimage sigma eventsA probeNode probeAppears
              have sigmaProbeBelow : sigma probePre < freshBase := by
                rw [probePreMaps]
                exact probeBelow
              have canonicalConnectedA : isSameComponent (applyJoinEvents eventsA [])
                  pivotCanonicalA probePre = true := by
                rw [← componentView_applyJoinEvents_ofRename sigma isInjective eventsA
                  pivotCanonicalA probePre, ← pivotNodeEq, probePreMaps]
                exact segmentConnected
              have transferred : isSameComponent (applyJoinEvents eventsB [])
                  pivotCanonicalB probePre = true :=
                canonicalTransfers pivotCanonicalA pivotCanonicalB probePre probePre
                  pivotPair (portPairsSelf probePre sigmaProbeBelow) canonicalConnectedA
              rw [pivotImageEq, ← probeSelfEq, ← probePreMaps,
                componentView_applyJoinEvents_ofRename sigma isInjective eventsB
                  pivotCanonicalB probePre]
              exact transferred
      | inr probePaired =>
          obtain ⟨probeCanonicalA, probeCanonicalB, probePair,
            probeNodeEq, probeImageEq⟩ := probePaired
          have canonicalConnectedA : isSameComponent (applyJoinEvents eventsA [])
              pivotCanonicalA probeCanonicalA = true := by
            rw [← componentView_applyJoinEvents_ofRename sigma isInjective eventsA
              pivotCanonicalA probeCanonicalA, ← pivotNodeEq, ← probeNodeEq]
            exact segmentConnected
          have transferred : isSameComponent (applyJoinEvents eventsB [])
              pivotCanonicalB probeCanonicalB = true :=
            canonicalTransfers pivotCanonicalA pivotCanonicalB
              probeCanonicalA probeCanonicalB pivotPair probePair canonicalConnectedA
          rw [pivotImageEq, probeImageEq,
            componentView_applyJoinEvents_ofRename sigma isInjective eventsB
              pivotCanonicalB probeCanonicalB]
          exact transferred

/-! ## The packaged composite transfer -/

/-- ★ **The composite transfer at the discharged relation** — brick 3's engine with
`InterfaceCorresponds` and the canonical-data segment discharge plugged in: composite
connectivity of the first renamed trace over the mid links transfers to the second at
corresponding probes, from canonical transfer data alone. -/
theorem isSameComponent_applyJoinEvents_transferAcrossInterface_ofCanonicalPairs
    (sigma : Nat → Nat)
    (isInjective : ∀ idOne idTwo : Nat, sigma idOne = sigma idTwo → idOne = idTwo)
    (freshBase : Nat) (CanonicalPair : Nat → Nat → Prop)
    (eventsA eventsB midLinks : List (Nat × Nat))
    (forest : isUnionFindForest midLinks)
    (baseBounded : ∀ leftNode rightNode : Nat, (leftNode, rightNode) ∈ midLinks →
      leftNode < freshBase ∧ rightNode < freshBase)
    (portPairsSelf : ∀ preimage : Nat, sigma preimage < freshBase →
      CanonicalPair preimage preimage)
    (canonicalTransfers : ∀ pivotCanonicalA pivotCanonicalB
        probeCanonicalA probeCanonicalB : Nat,
      CanonicalPair pivotCanonicalA pivotCanonicalB →
      CanonicalPair probeCanonicalA probeCanonicalB →
      isSameComponent (applyJoinEvents eventsA []) pivotCanonicalA probeCanonicalA = true →
      isSameComponent (applyJoinEvents eventsB []) pivotCanonicalB probeCanonicalB = true)
    (startNode lastNode startImage lastImage : Nat)
    (startCorresponds : InterfaceCorresponds sigma freshBase CanonicalPair
      startNode startImage)
    (lastCorresponds : InterfaceCorresponds sigma freshBase CanonicalPair
      lastNode lastImage)
    (foldConnected : isSameComponent
      (applyJoinEvents (eventsA.map (fun event => (sigma event.1, sigma event.2))) midLinks)
      startNode lastNode = true) :
    isSameComponent
      (applyJoinEvents (eventsB.map (fun event => (sigma event.1, sigma event.2))) midLinks)
      startImage lastImage = true :=
  isSameComponent_applyJoinEvents_transferAcrossInterface
    (eventsA.map (fun event => (sigma event.1, sigma event.2)))
    (eventsB.map (fun event => (sigma event.1, sigma event.2)))
    midLinks freshBase (InterfaceCorresponds sigma freshBase CanonicalPair)
    forest baseBounded
    (interfaceCorresponds_ofBelowBase sigma freshBase CanonicalPair)
    (segmentTransfers_ofCanonicalPairs sigma isInjective freshBase CanonicalPair
      eventsA eventsB portPairsSelf canonicalTransfers)
    startNode lastNode startImage lastImage startCorresponds lastCorresponds foldConnected

/-! ## Honesty marker -/

/-- **Honesty marker — the segment-transfer discharge is SHIPPED.**  The interface-transfer
engine's semantic hypothesis now follows from canonical-level data alone
(`segmentTransfers_ofCanonicalPairs`): an injective zone-disciplined rename, below-base ports
self-pairing, and the canonical transfer at paired probes — via the decidable trace-support
split (rigidity for untouched probes, port-preimage extraction for touched ones) and rename
equivariance in both directions.  Packaged as the one-directional composite transfer
(`…_transferAcrossInterface_ofCanonicalPairs`).  NOT yet shipped: instantiating
`CanonicalPair` at the positional boundary pairing of two extract-equal canonical runs and
the composite-boundary `Corresponds` instances — the VIEW leg's closing brick — and the LOOP
leg.  `= true`. -/
def fxMode_hasInterfaceSegmentDischarge : Bool := true

end FX1Poly.Polygraph
