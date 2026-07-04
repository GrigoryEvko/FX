import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventExchange

/-! # MatchingLinksAsEvents — a links list replayed as events + the exchange decomposition (MODE3-D)

The LOOP leg compares loop counts over the mid-state links; the exchange machinery
(`countJoinEventLoops_append` / `_append_comm`) compares counts over EVENT folds.  This file
bridges the two: a forest links list, replayed as a join-event trace over the empty base,
reconstructs exactly its own component view — so the mid-links base can be swapped for a fold
and the whole block-exchange calculus applies.

* `sameComponent_ofLinkMember` — every stored edge relates its endpoints (structural induction
  through `unionFindRootOf_consJoin`, the forest keeping every cons a fresh root→root edge);
* `foldConnected_ofLinksView` / `linksView_ofFoldConnected` — the two directions: root-chasing
  is fold-connectivity (a fuel walk chaining each parent hop through `_ofMem`), and the fold
  lifts back into the links' own view (`_lift` with the stored-edge completeness);
* ★ `componentView_applyJoinEvents_selfLinks` — the Bool-level self-replay view equality;
* ★ `countJoinEventLoops_overLinks_exchange` — the additive exchange decomposition:
  `count(midLinks, []) + count(events, midLinks)
     = count(events, []) + count(midLinks, fold(events, []))` — the loop count over a mid-state
  base reduced to empty-base counts plus the mid edges' count over the trace's own fold.

With the count rename invariance (`MatchingCountRename`) this leaves the LOOP leg needing only
the mid-node view agreement between the two renamed folds.  Raw Lean 4 + Init;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing -/

private theorem boolEqOfImpliesBoth : (leftBool rightBool : Bool) →
    (leftBool = true → rightBool = true) → (rightBool = true → leftBool = true) →
    leftBool = rightBool
  | true, _, forward, _ => (forward rfl).symm
  | false, true, _, backward => backward rfl
  | false, false, _, _ => rfl

private theorem natBeqSelf (node : Nat) : (node == node) = true := decide_eq_true rfl

private theorem boolFalse_ofNotTrue : (flag : Bool) → ¬ flag = true → flag = false
  | true, notTrue => absurd rfl notTrue
  | false, _ => rfl

/-- Cons-membership decomposition (core iff lemmas leak propext). -/
private theorem memberConsCases {Element : Type} (candidate headElement : Element)
    (restElements : List Element) (membership : candidate ∈ headElement :: restElements) :
    candidate = headElement ∨ candidate ∈ restElements := by
  cases membership with
  | head => exact Or.inl rfl
  | tail _ restMembership => exact Or.inr restMembership

/-- A successful parent lookup is a stored edge. -/
private theorem linkMember_ofParentLookup :
    (links : List (Nat × Nat)) → (node parentNode : Nat) →
    unionFindParent links node = some parentNode → (node, parentNode) ∈ links
  | [], _, _, lookupEq => nomatch lookupEq
  | (childHead, parentHead) :: restLinks, node, parentNode, lookupEq => by
      cases headTest : childHead == node with
      | true =>
          have childEqNode : childHead = node := of_decide_eq_true headTest
          have shaped : (if childHead == node then some parentHead
              else unionFindParent restLinks node) = some parentNode := lookupEq
          rw [headTest] at shaped
          have parentsEqual : some parentHead = some parentNode := shaped
          have parentEqNode : parentHead = parentNode := Option.some.inj parentsEqual
          rw [← childEqNode, ← parentEqNode]
          exact List.Mem.head restLinks
      | false =>
          have shaped : (if childHead == node then some parentHead
              else unionFindParent restLinks node) = some parentNode := lookupEq
          rw [headTest] at shaped
          have restLookup : unionFindParent restLinks node = some parentNode := shaped
          exact List.Mem.tail (childHead, parentHead)
            (linkMember_ofParentLookup restLinks node parentNode restLookup)

/-! ## Stored edges relate their endpoints -/

/-- **Every stored edge relates its endpoints in its own list** (forest-conditioned).  Structural
induction: the head edge routes both endpoints to the parent through `unionFindRootOf_consJoin`;
a tail edge's roots agree in the rest and the head cons redirects both reads identically. -/
theorem sameComponent_ofLinkMember :
    (links : List (Nat × Nat)) → isUnionFindForest links → (child parentNode : Nat) →
    (child, parentNode) ∈ links → isSameComponent links child parentNode = true
  | [], _, _, _, membership => by cases membership
  | (edgeChild, edgeParent) :: restLinks, forest, child, parentNode, membership => by
      have childParentless : unionFindParent restLinks edgeChild = none := forest.1
      have parentParentless : unionFindParent restLinks edgeParent = none := forest.2.1
      have endpointsDistinct : ¬ (edgeChild == edgeParent) = true := forest.2.2.1
      have restForest : isUnionFindForest restLinks := forest.2.2.2
      have consRoot : ∀ probeNode : Nat,
          unionFindRootOf ((edgeChild, edgeParent) :: restLinks) probeNode
            = (if edgeChild == unionFindRootOf restLinks probeNode then edgeParent
                else unionFindRootOf restLinks probeNode) :=
        fun probeNode => unionFindRootOf_consJoin restLinks edgeChild edgeParent restForest
          childParentless parentParentless endpointsDistinct probeNode
      cases memberConsCases (child, parentNode) (edgeChild, edgeParent) restLinks
          membership with
      | inl pairEqual =>
          have childEqual : child = edgeChild := congrArg Prod.fst pairEqual
          have parentEqual : parentNode = edgeParent := congrArg Prod.snd pairEqual
          rw [childEqual, parentEqual]
          show (unionFindRootOf ((edgeChild, edgeParent) :: restLinks) edgeChild
              == unionFindRootOf ((edgeChild, edgeParent) :: restLinks) edgeParent) = true
          rw [consRoot edgeChild, consRoot edgeParent,
            unionFindRootOf_of_parentless restLinks edgeChild childParentless,
            unionFindRootOf_of_parentless restLinks edgeParent parentParentless,
            natBeqSelf edgeChild,
            boolFalse_ofNotTrue (edgeChild == edgeParent) endpointsDistinct]
          exact natBeqSelf edgeParent
      | inr restMembership =>
          have restView : isSameComponent restLinks child parentNode = true :=
            sameComponent_ofLinkMember restLinks restForest child parentNode restMembership
          have rootsEqual : unionFindRootOf restLinks child
              = unionFindRootOf restLinks parentNode := of_decide_eq_true restView
          show (unionFindRootOf ((edgeChild, edgeParent) :: restLinks) child
              == unionFindRootOf ((edgeChild, edgeParent) :: restLinks) parentNode) = true
          rw [consRoot child, consRoot parentNode, rootsEqual]
          exact natBeqSelf _

/-! ## The two directions of the self-replay -/

/-- Every node is fold-connected to its own root: the fuel walk chains one stored-edge hop
(`_ofMem` on the looked-up parent) at a time. -/
private theorem foldConnected_toUnionFindRoot (links : List (Nat × Nat)) :
    (fuel : Nat) → (node : Nat) →
    isSameComponent (applyJoinEvents links []) node (unionFindRoot fuel links node) = true
  | 0, node => by
      show (unionFindRootOf (applyJoinEvents links []) node
          == unionFindRootOf (applyJoinEvents links []) node) = true
      exact natBeqSelf _
  | fuel + 1, node => by
      cases parentLookup : unionFindParent links node with
      | none =>
          have rootStops : unionFindRoot (fuel + 1) links node = node := by
            show (match unionFindParent links node with
                  | none => node
                  | some parentStep => unionFindRoot fuel links parentStep) = node
            rw [parentLookup]
          rw [rootStops]
          show (unionFindRootOf (applyJoinEvents links []) node
              == unionFindRootOf (applyJoinEvents links []) node) = true
          exact natBeqSelf _
      | some parentNode =>
          have rootFollows : unionFindRoot (fuel + 1) links node
              = unionFindRoot fuel links parentNode := by
            show (match unionFindParent links node with
                  | none => node
                  | some parentStep => unionFindRoot fuel links parentStep)
                = unionFindRoot fuel links parentNode
            rw [parentLookup]
          rw [rootFollows]
          exact isSameComponent_trans (applyJoinEvents links []) node parentNode
            (unionFindRoot fuel links parentNode)
            (isSameComponent_applyJoinEvents_ofMem links [] True.intro node parentNode
              (linkMember_ofParentLookup links node parentNode parentLookup))
            (foldConnected_toUnionFindRoot links fuel parentNode)

/-- Links-view connectivity replays in the fold: both probes walk to their (equal) roots. -/
theorem foldConnected_ofLinksView (links : List (Nat × Nat)) (probeOne probeTwo : Nat)
    (linksView : isSameComponent links probeOne probeTwo = true) :
    isSameComponent (applyJoinEvents links []) probeOne probeTwo = true := by
  have rootsEqual : unionFindRootOf links probeOne = unionFindRootOf links probeTwo :=
    of_decide_eq_true linksView
  have oneToRoot : isSameComponent (applyJoinEvents links []) probeOne
      (unionFindRootOf links probeOne) = true :=
    foldConnected_toUnionFindRoot links (links.length + 1) probeOne
  have twoToRoot : isSameComponent (applyJoinEvents links []) probeTwo
      (unionFindRootOf links probeTwo) = true :=
    foldConnected_toUnionFindRoot links (links.length + 1) probeTwo
  rw [rootsEqual] at oneToRoot
  exact isSameComponent_trans (applyJoinEvents links []) probeOne
    (unionFindRootOf links probeTwo) probeTwo oneToRoot
    (isSameComponent_flip (applyJoinEvents links []) probeTwo
      (unionFindRootOf links probeTwo) twoToRoot)

/-- Fold connectivity lifts back into the links' own view: the empty base forces node equality
and every replayed event is a stored edge (`sameComponent_ofLinkMember`). -/
theorem linksView_ofFoldConnected (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (probeOne probeTwo : Nat)
    (foldConnected : isSameComponent (applyJoinEvents links []) probeOne probeTwo = true) :
    isSameComponent links probeOne probeTwo = true :=
  isSameComponent_applyJoinEvents_lift links [] links True.intro
    (fun nodeOne nodeTwo emptyView => by
      have nodesEqual : nodeOne = nodeTwo := of_decide_eq_true emptyView
      cases nodesEqual
      exact natBeqSelf _)
    (fun firstNode secondNode membership =>
      sameComponent_ofLinkMember links forest firstNode secondNode membership)
    probeOne probeTwo foldConnected

/-- ★ **A forest links list replayed as events reconstructs its own component view.** -/
theorem componentView_applyJoinEvents_selfLinks (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (probeOne probeTwo : Nat) :
    isSameComponent (applyJoinEvents links []) probeOne probeTwo
      = isSameComponent links probeOne probeTwo :=
  boolEqOfImpliesBoth _ _
    (linksView_ofFoldConnected links forest probeOne probeTwo)
    (foldConnected_ofLinksView links probeOne probeTwo)

/-! ## The exchange decomposition -/

/-- ★ **The additive exchange decomposition of a count over a mid-state base.**  Swap the base
for its self-replay fold (`countJoinEventLoops_congr` + the self-replay view), fuse the two
blocks (`countJoinEventLoops_append`), and transpose them (`countJoinEventLoops_append_comm`):
the count over the mid links reduces to empty-base counts plus the mid edges' count over the
trace's own fold. -/
theorem countJoinEventLoops_overLinks_exchange (events midLinks : List (Nat × Nat))
    (midForest : isUnionFindForest midLinks) :
    countJoinEventLoops midLinks [] + countJoinEventLoops events midLinks
      = countJoinEventLoops events []
          + countJoinEventLoops midLinks (applyJoinEvents events []) := by
  have countOnFoldBase : countJoinEventLoops events (applyJoinEvents midLinks [])
      = countJoinEventLoops events midLinks :=
    countJoinEventLoops_congr events (applyJoinEvents midLinks []) midLinks
      (isUnionFindForest_applyJoinEvents midLinks [] True.intro) midForest
      (fun probeOne probeTwo =>
        componentView_applyJoinEvents_selfLinks midLinks midForest probeOne probeTwo)
  rw [← countOnFoldBase, ← countJoinEventLoops_append midLinks events [],
    countJoinEventLoops_append_comm midLinks events [] True.intro,
    countJoinEventLoops_append events midLinks []]

/-- **Honesty marker — the links-as-events self-replay + exchange decomposition are PROVED.**
Shipped: stored edges relate their endpoints, the two-directional self-replay view equality,
and the additive exchange decomposition over a mid-state base.  NOT yet shipped: the mid-node
view agreement between the two renamed folds and the final loop-increment equality glue. -/
def fxMode_hasLinksAsEventsExchange : Bool := true

end FX1Poly.Polygraph
