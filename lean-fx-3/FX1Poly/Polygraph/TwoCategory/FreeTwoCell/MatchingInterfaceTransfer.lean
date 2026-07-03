import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventPath
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision

/-! # MatchingInterfaceTransfer — composite connectivity transfers across the interface (MODE3-D)

The VIEW-leg locality argument: two second-half event traces over the SAME mid-state links have
pointwise-corresponding composite connectivity, provided their EMPTY-BASE folds correspond at
related probes.  The walk is brick 2's alternating path with a pivot/pending invariant:

* event steps only EXTEND the pending empty-base segment (no goodness needed mid-segment);
* a nontrivial base step forces BOTH its endpoints below the fresh base
  (`firstEndpointBelow_ofNontrivialBaseConnected`: a node at or above the base is its own root,
  and roots of below-base nodes stay below — so the roots cannot meet), and below-base nodes
  SELF-correspond, so the pending segment closes through the segment-transfer hypothesis, the
  base edge crosses shared, and a fresh trivial segment opens;
* at the path's end the last pending segment closes against the given end correspondence.

`Corresponds` abstracts the D5 instantiation: below-base identifiers self-correspond (mid ports
and gamma-side wires alike — for untouched non-ports the segment transfer is vacuous since an
empty-base connection of an untouched node forces equality), and each composite's top wires
correspond positionally.  ★ `isSameComponent_applyJoinEvents_transferAcrossInterface` is the
whole one-directional engine from raw fold connectivity.  Raw Lean 4 + Init; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Empty-base plumbing -/

/-- Over the empty base every node is its own root, so empty-base connectivity forces
equality. -/
theorem nodesEqual_ofEmptyBaseConnected (firstNode secondNode : Nat)
    (connected : isSameComponent [] firstNode secondNode = true) :
    firstNode = secondNode := by
  have rootsEqual : unionFindRootOf [] firstNode = unionFindRootOf [] secondNode :=
    of_decide_eq_true connected
  rw [unionFindRootOf_eq_self_ofFresh 0 [] (fun edge edgeInNil => by cases edgeInNil)
      firstNode (Nat.zero_le firstNode),
    unionFindRootOf_eq_self_ofFresh 0 [] (fun edge edgeInNil => by cases edgeInNil)
      secondNode (Nat.zero_le secondNode)] at rootsEqual
  exact rootsEqual

/-- Empty-base fold connectivity embeds into the fold over ANY forest base — the fold universal
property with the loaded fold as target (empty-base facts are equalities, event pairs by
completeness). -/
theorem isSameComponent_applyJoinEvents_ofEmptyBase (events links : List (Nat × Nat))
    (forest : isUnionFindForest links) (firstNode secondNode : Nat)
    (emptyFoldConnected :
      isSameComponent (applyJoinEvents events []) firstNode secondNode = true) :
    isSameComponent (applyJoinEvents events links) firstNode secondNode = true :=
  isSameComponent_applyJoinEvents_lift events [] (applyJoinEvents events links)
    True.intro
    (fun nodeOne nodeTwo emptyConnected => by
      rw [nodesEqual_ofEmptyBaseConnected nodeOne nodeTwo emptyConnected]
      exact isSameComponent_self (applyJoinEvents events links) nodeTwo)
    (fun eventFirst eventSecond eventListed =>
      isSameComponent_applyJoinEvents_ofMem events links forest eventFirst eventSecond
        eventListed)
    firstNode secondNode emptyFoldConnected

/-! ## Nontrivial base connectivity pins its endpoints below the base -/

/-- **A nontrivial base connection cannot reach at or above the fresh base**: an at-or-above
node is its own root (out of the union-find's support), while the other endpoint's root is
either itself (again at-or-above, forcing the nodes equal) or below the base (so the roots
cannot meet). -/
theorem firstEndpointBelow_ofNontrivialBaseConnected
    (midLinks : List (Nat × Nat)) (freshBase : Nat)
    (baseBounded : ∀ leftNode rightNode : Nat, (leftNode, rightNode) ∈ midLinks →
      leftNode < freshBase ∧ rightNode < freshBase)
    (firstNode secondNode : Nat) (nodesDiffer : firstNode ≠ secondNode)
    (baseConnected : isSameComponent midLinks firstNode secondNode = true) :
    firstNode < freshBase := by
  cases Nat.lt_or_ge firstNode freshBase with
  | inl firstBelow => exact firstBelow
  | inr firstAtLeast =>
      have childBounded : ∀ edge ∈ midLinks, edge.1 < freshBase :=
        fun edge edgeListed => (baseBounded edge.1 edge.2 edgeListed).1
      have parentBounded : ∀ edge ∈ midLinks, edge.2 < freshBase :=
        fun edge edgeListed => (baseBounded edge.1 edge.2 edgeListed).2
      have rootsEqual : unionFindRootOf midLinks firstNode
          = unionFindRootOf midLinks secondNode :=
        of_decide_eq_true baseConnected
      rw [unionFindRootOf_eq_self_ofFresh freshBase midLinks childBounded firstNode
        firstAtLeast] at rootsEqual
      cases Nat.lt_or_ge secondNode freshBase with
      | inl secondBelow =>
          have rootSecondBelow : unionFindRootOf midLinks secondNode < freshBase :=
            unionFindRootOf_lt freshBase midLinks parentBounded secondNode secondBelow
          rw [← rootsEqual] at rootSecondBelow
          exact absurd (Nat.lt_of_lt_of_le rootSecondBelow firstAtLeast)
            (Nat.lt_irrefl firstNode)
      | inr secondAtLeast =>
          rw [unionFindRootOf_eq_self_ofFresh freshBase midLinks childBounded secondNode
            secondAtLeast] at rootsEqual
          exact absurd rootsEqual nodesDiffer

/-! ## The transfer engine -/

/-- **The pivot/pending walk**: transfer an alternating path of the first composite into
connectivity of the second, threading (a) the accumulated second-composite connection from the
start image to the current pivot's image, and (b) the pending first-trace empty-base segment
from the pivot to the current node.  Event steps extend the pending segment; nontrivial base
steps close it at a below-base (hence self-corresponding) switch node, cross the shared base
edge, and reopen; the end correspondence closes the final segment. -/
theorem transferAlongJoinEventPath
    (eventsA eventsB midLinks : List (Nat × Nat)) (freshBase : Nat)
    (Corresponds : Nat → Nat → Prop)
    (forest : isUnionFindForest midLinks)
    (baseBounded : ∀ leftNode rightNode : Nat, (leftNode, rightNode) ∈ midLinks →
      leftNode < freshBase ∧ rightNode < freshBase)
    (belowBaseCorresponds : ∀ node : Nat, node < freshBase → Corresponds node node)
    (segmentTransfers : ∀ pivotNode probeNode pivotImage probeImage : Nat,
      Corresponds pivotNode pivotImage → Corresponds probeNode probeImage →
      isSameComponent (applyJoinEvents eventsA []) pivotNode probeNode = true →
      isSameComponent (applyJoinEvents eventsB []) pivotImage probeImage = true)
    (currentNode lastNode : Nat)
    (path : JoinEventPath eventsA midLinks currentNode lastNode) :
    ∀ startImage pivotNode pivotImage : Nat,
      Corresponds pivotNode pivotImage →
      isSameComponent (applyJoinEvents eventsB midLinks) startImage pivotImage = true →
      isSameComponent (applyJoinEvents eventsA []) pivotNode currentNode = true →
      ∀ lastImage : Nat, Corresponds lastNode lastImage →
      isSameComponent (applyJoinEvents eventsB midLinks) startImage lastImage = true := by
  induction path with
  | refl node =>
      intro startImage pivotNode pivotImage pivotCorresponds accumulated pending
        lastImage lastCorresponds
      exact isSameComponent_trans (applyJoinEvents eventsB midLinks) startImage pivotImage
        lastImage accumulated
        (isSameComponent_applyJoinEvents_ofEmptyBase eventsB midLinks forest pivotImage
          lastImage
          (segmentTransfers pivotNode node pivotImage lastImage pivotCorresponds
            lastCorresponds pending))
  | cons stepFirst stepMiddle stepLast headStep restPath transferRest =>
      intro startImage pivotNode pivotImage pivotCorresponds accumulated pending
        lastImage lastCorresponds
      cases headStep with
      | ofEvent eventListed =>
          exact transferRest startImage pivotNode pivotImage pivotCorresponds accumulated
            (isSameComponent_trans (applyJoinEvents eventsA []) pivotNode stepFirst stepMiddle
              pending
              (isSameComponent_applyJoinEvents_ofMem eventsA [] True.intro stepFirst
                stepMiddle eventListed))
            lastImage lastCorresponds
      | ofEventFlipped eventListed =>
          exact transferRest startImage pivotNode pivotImage pivotCorresponds accumulated
            (isSameComponent_trans (applyJoinEvents eventsA []) pivotNode stepFirst stepMiddle
              pending
              (isSameComponent_flip (applyJoinEvents eventsA []) stepMiddle stepFirst
                (isSameComponent_applyJoinEvents_ofMem eventsA [] True.intro stepMiddle
                  stepFirst eventListed)))
            lastImage lastCorresponds
      | ofBase baseConnected =>
          cases Nat.decEq stepFirst stepMiddle with
          | isTrue nodesEqual =>
              exact transferRest startImage pivotNode pivotImage pivotCorresponds accumulated
                (nodesEqual ▸ pending) lastImage lastCorresponds
          | isFalse nodesDiffer =>
              have stepFirstBelow : stepFirst < freshBase :=
                firstEndpointBelow_ofNontrivialBaseConnected midLinks freshBase baseBounded
                  stepFirst stepMiddle nodesDiffer baseConnected
              have stepMiddleBelow : stepMiddle < freshBase :=
                firstEndpointBelow_ofNontrivialBaseConnected midLinks freshBase baseBounded
                  stepMiddle stepFirst (fun middleEqFirst => nodesDiffer middleEqFirst.symm)
                  (isSameComponent_flip midLinks stepFirst stepMiddle baseConnected)
              have closedSegment : isSameComponent (applyJoinEvents eventsB midLinks)
                  pivotImage stepFirst = true :=
                isSameComponent_applyJoinEvents_ofEmptyBase eventsB midLinks forest pivotImage
                  stepFirst
                  (segmentTransfers pivotNode stepFirst pivotImage stepFirst pivotCorresponds
                    (belowBaseCorresponds stepFirst stepFirstBelow) pending)
              have crossedBase : isSameComponent (applyJoinEvents eventsB midLinks)
                  stepFirst stepMiddle = true :=
                isSameComponent_applyJoinEvents_ofBase eventsB midLinks forest stepFirst
                  stepMiddle baseConnected
              exact transferRest startImage stepMiddle stepMiddle
                (belowBaseCorresponds stepMiddle stepMiddleBelow)
                (isSameComponent_trans (applyJoinEvents eventsB midLinks) startImage stepFirst
                  stepMiddle
                  (isSameComponent_trans (applyJoinEvents eventsB midLinks) startImage
                    pivotImage stepFirst accumulated closedSegment)
                  crossedBase)
                (isSameComponent_self (applyJoinEvents eventsA []) stepMiddle)
                lastImage lastCorresponds

/-- ★ **The interface transfer** — composite connectivity of the first trace transfers to the
second at corresponding probes: decompose into brick 2's alternating path and run the
pivot/pending walk from trivial initial accumulator and segment. -/
theorem isSameComponent_applyJoinEvents_transferAcrossInterface
    (eventsA eventsB midLinks : List (Nat × Nat)) (freshBase : Nat)
    (Corresponds : Nat → Nat → Prop)
    (forest : isUnionFindForest midLinks)
    (baseBounded : ∀ leftNode rightNode : Nat, (leftNode, rightNode) ∈ midLinks →
      leftNode < freshBase ∧ rightNode < freshBase)
    (belowBaseCorresponds : ∀ node : Nat, node < freshBase → Corresponds node node)
    (segmentTransfers : ∀ pivotNode probeNode pivotImage probeImage : Nat,
      Corresponds pivotNode pivotImage → Corresponds probeNode probeImage →
      isSameComponent (applyJoinEvents eventsA []) pivotNode probeNode = true →
      isSameComponent (applyJoinEvents eventsB []) pivotImage probeImage = true)
    (startNode lastNode startImage lastImage : Nat)
    (startCorresponds : Corresponds startNode startImage)
    (lastCorresponds : Corresponds lastNode lastImage)
    (foldConnected :
      isSameComponent (applyJoinEvents eventsA midLinks) startNode lastNode = true) :
    isSameComponent (applyJoinEvents eventsB midLinks) startImage lastImage = true :=
  transferAlongJoinEventPath eventsA eventsB midLinks freshBase Corresponds forest baseBounded
    belowBaseCorresponds segmentTransfers startNode lastNode
    (joinEventPath_ofFold eventsA midLinks forest startNode lastNode foldConnected)
    startImage startNode startImage startCorresponds
    (isSameComponent_self (applyJoinEvents eventsB midLinks) startImage)
    (isSameComponent_self (applyJoinEvents eventsA []) startNode)
    lastImage lastCorresponds

/-! ## Honesty marker -/

/-- **Honesty marker — the interface transfer engine is SHIPPED.**  Composite fold connectivity
transfers between two second-half traces over shared mid-state links at corresponding probes,
given only: base entries bounded below the fresh base, below-base identifiers self-correspond,
and the two EMPTY-BASE folds correspond at related probes (the form extract equality + rename
equivariance discharge).  NOT yet shipped: the D5 instantiation — building `Corresponds` from
the two relative runs' wire simulations and discharging the segment-transfer hypothesis from
canonical extract equality through `componentView_ofFreshRename`; and the LOOP leg.  `= true`. -/
def fxMode_hasInterfaceChainTransfer : Bool := true

end FX1Poly.Polygraph
