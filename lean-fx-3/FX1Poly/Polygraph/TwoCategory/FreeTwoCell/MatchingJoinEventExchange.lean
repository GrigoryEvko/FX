import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEvents

/-! # mode-3 keystone — the block exchange of join-event traces

The sigma witness compares the two transposed Godement orders' partitions, and neither order's
intermediate states correspond — the comparison lives at the level of REIFIED traces
(`MatchingJoinEvents`).  This file ships the pure combinatorial half: transposing two BLOCKS of a
join-event trace (at fixed node ids) is invisible to the partition.

  * ★ `componentView_applyJoinEvents_ofMemEquiv` — the same-component view of an event fold depends
    only on the MEMBERSHIP of the trace: any two mem-equivalent event lists produce pointwise-equal
    views.  Proof = double elimination through the list-level universal property
    (`isSameComponent_applyJoinEvents_lift`, folding the banked single-join `_lift`), with
    completeness (`_ofMem`) and monotone extension (`_ofBase`) supplying the two inclusions.
    `componentView_applyJoinEvents_append_comm` specializes to the block swap.
  * ★ `countJoinEventLoops_append_comm` — the LOOP COUNT of a trace is also block-swap invariant.
    Membership is too weak here (counts see multiplicity), so the proof is a genuine double
    induction: the cross-exchange (`countJoinEventLoops_crossExchange`) peels the first block one
    event at a time, and each peeled event commutes past the whole second block by
    `countJoinEventLoops_singleJoinExchange`, whose inductive step is EXACTLY the banked two-cap
    increment exchange (`sameComponentIncrement_unionFindJoin_swap`) plus the banked two-join view
    swap (`isSameComponent_unionFindJoin_swap`) transported through the count congruence.
  * Congruence infrastructure: the view and the count are functions of the links' component VIEW
    only (`componentView_applyJoinEvents_congr`, `countJoinEventLoops_congr`), so view-equal link
    lists are interchangeable under any further trace.

NOT yet covered (the next brick): the cross-order trace CORRESPONDENCE — that the two Godement
orders' traces are a `blockRotate`-rename plus a block swap of each other; with it, `componentComm`
= sigma-equivariance ∘ this exchange.  Raw Lean 4 + Init; structural recursion only;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Boolean and membership plumbing -/

private theorem boolEqOfImpliesBoth : (leftBool rightBool : Bool) →
    (leftBool = true → rightBool = true) → (rightBool = true → leftBool = true) →
    leftBool = rightBool
  | false, false, _, _ => rfl
  | false, true, _, backward => backward rfl
  | true, false, forward, _ => (forward rfl).symm
  | true, true, _, _ => rfl

private theorem pairMemAppendOfLeft :
    (leftList rightList : List (Nat × Nat)) → (event : Nat × Nat) → event ∈ leftList →
    event ∈ leftList ++ rightList
  | [], _, _, membership => by cases membership
  | headEvent :: restLeft, rightList, event, membership => by
      cases membership with
      | head => exact List.Mem.head (restLeft ++ rightList)
      | tail _ tailMembership =>
          exact List.Mem.tail headEvent
            (pairMemAppendOfLeft restLeft rightList event tailMembership)

private theorem pairMemAppendOfRight :
    (leftList rightList : List (Nat × Nat)) → (event : Nat × Nat) → event ∈ rightList →
    event ∈ leftList ++ rightList
  | [], _, _, membership => membership
  | headEvent :: restLeft, rightList, event, membership =>
      List.Mem.tail headEvent (pairMemAppendOfRight restLeft rightList event membership)

private theorem pairMemAppendCases :
    (leftList rightList : List (Nat × Nat)) → (event : Nat × Nat) →
    event ∈ leftList ++ rightList → event ∈ leftList ∨ event ∈ rightList
  | [], _, _, membership => Or.inr membership
  | headEvent :: restLeft, rightList, event, membership => by
      cases membership with
      | head => exact Or.inl (List.Mem.head restLeft)
      | tail _ tailMembership =>
          cases pairMemAppendCases restLeft rightList event tailMembership with
          | inl inLeft => exact Or.inl (List.Mem.tail headEvent inLeft)
          | inr inRight => exact Or.inr inRight

/-- The event fold preserves the forest invariant (each event is one join). -/
theorem isUnionFindForest_applyJoinEvents :
    (events : List (Nat × Nat)) → (links : List (Nat × Nat)) → isUnionFindForest links →
    isUnionFindForest (applyJoinEvents events links)
  | [], _, forest => forest
  | (firstNode, secondNode) :: restEvents, links, forest =>
      isUnionFindForest_applyJoinEvents restEvents (unionFindJoin links firstNode secondNode)
        (isUnionFindForest_unionFindJoin links firstNode secondNode forest)

/-! ## The view and the count are functions of the component view -/

/-- One join at the same pair over view-equal link lists yields view-equal link lists — read both
sides off the flat-disjunction characterization and rewrite the five atoms. -/
theorem isSameComponent_unionFindJoin_congr (linksOne linksTwo : List (Nat × Nat))
    (forestOne : isUnionFindForest linksOne) (forestTwo : isUnionFindForest linksTwo)
    (viewsAgree : ∀ nodeOne nodeTwo : Nat,
      isSameComponent linksOne nodeOne nodeTwo = isSameComponent linksTwo nodeOne nodeTwo)
    (joinLeft joinRight probeOne probeTwo : Nat) :
    isSameComponent (unionFindJoin linksOne joinLeft joinRight) probeOne probeTwo
      = isSameComponent (unionFindJoin linksTwo joinLeft joinRight) probeOne probeTwo := by
  rw [isSameComponent_unionFindJoin linksOne forestOne joinLeft joinRight probeOne probeTwo,
    isSameComponent_unionFindJoin linksTwo forestTwo joinLeft joinRight probeOne probeTwo,
    viewsAgree probeOne probeTwo, viewsAgree joinLeft probeOne, viewsAgree joinRight probeTwo,
    viewsAgree joinLeft probeTwo, viewsAgree probeOne joinRight]

/-- The whole event fold is a congruence in the links argument: view-equal inputs give view-equal
outputs (forests threaded through the joins). -/
theorem componentView_applyJoinEvents_congr :
    (events : List (Nat × Nat)) → (linksOne linksTwo : List (Nat × Nat)) →
    isUnionFindForest linksOne → isUnionFindForest linksTwo →
    (∀ nodeOne nodeTwo : Nat,
      isSameComponent linksOne nodeOne nodeTwo = isSameComponent linksTwo nodeOne nodeTwo) →
    ∀ probeOne probeTwo : Nat,
    isSameComponent (applyJoinEvents events linksOne) probeOne probeTwo
      = isSameComponent (applyJoinEvents events linksTwo) probeOne probeTwo
  | [], _, _, _, _, viewsAgree, probeOne, probeTwo => viewsAgree probeOne probeTwo
  | (firstNode, secondNode) :: restEvents, linksOne, linksTwo, forestOne, forestTwo,
      viewsAgree, probeOne, probeTwo =>
      componentView_applyJoinEvents_congr restEvents
        (unionFindJoin linksOne firstNode secondNode)
        (unionFindJoin linksTwo firstNode secondNode)
        (isUnionFindForest_unionFindJoin linksOne firstNode secondNode forestOne)
        (isUnionFindForest_unionFindJoin linksTwo firstNode secondNode forestTwo)
        (fun nodeOne nodeTwo => isSameComponent_unionFindJoin_congr linksOne linksTwo
          forestOne forestTwo viewsAgree firstNode secondNode nodeOne nodeTwo)
        probeOne probeTwo

/-- The loop count is a congruence in the links argument: each event's test reads only the view,
and the view correspondence survives the join. -/
theorem countJoinEventLoops_congr :
    (events : List (Nat × Nat)) → (linksOne linksTwo : List (Nat × Nat)) →
    isUnionFindForest linksOne → isUnionFindForest linksTwo →
    (∀ nodeOne nodeTwo : Nat,
      isSameComponent linksOne nodeOne nodeTwo = isSameComponent linksTwo nodeOne nodeTwo) →
    countJoinEventLoops events linksOne = countJoinEventLoops events linksTwo
  | [], _, _, _, _, _ => rfl
  | (firstNode, secondNode) :: restEvents, linksOne, linksTwo, forestOne, forestTwo,
      viewsAgree => by
      show (isSameComponent linksOne firstNode secondNode).toNat
            + countJoinEventLoops restEvents (unionFindJoin linksOne firstNode secondNode)
          = (isSameComponent linksTwo firstNode secondNode).toNat
              + countJoinEventLoops restEvents (unionFindJoin linksTwo firstNode secondNode)
      rw [viewsAgree firstNode secondNode,
        countJoinEventLoops_congr restEvents
          (unionFindJoin linksOne firstNode secondNode)
          (unionFindJoin linksTwo firstNode secondNode)
          (isUnionFindForest_unionFindJoin linksOne firstNode secondNode forestOne)
          (isUnionFindForest_unionFindJoin linksTwo firstNode secondNode forestTwo)
          (fun nodeOne nodeTwo => isSameComponent_unionFindJoin_congr linksOne linksTwo
            forestOne forestTwo viewsAgree firstNode secondNode nodeOne nodeTwo)]

/-! ## The list-level universal property of the event fold -/

/-- Monotone extension: base membership survives the whole event fold. -/
theorem isSameComponent_applyJoinEvents_ofBase :
    (events : List (Nat × Nat)) → (links : List (Nat × Nat)) → isUnionFindForest links →
    (probeOne probeTwo : Nat) → isSameComponent links probeOne probeTwo = true →
    isSameComponent (applyJoinEvents events links) probeOne probeTwo = true
  | [], _, _, _, _, base => base
  | (firstNode, secondNode) :: restEvents, links, forest, probeOne, probeTwo, base =>
      isSameComponent_applyJoinEvents_ofBase restEvents
        (unionFindJoin links firstNode secondNode)
        (isUnionFindForest_unionFindJoin links firstNode secondNode forest)
        probeOne probeTwo
        (isSameComponent_unionFindJoin_ofBase links forest firstNode secondNode
          probeOne probeTwo base)

/-- Completeness: the fold relates every event pair of its trace. -/
theorem isSameComponent_applyJoinEvents_ofMem :
    (events : List (Nat × Nat)) → (links : List (Nat × Nat)) → isUnionFindForest links →
    (firstNode secondNode : Nat) → (firstNode, secondNode) ∈ events →
    isSameComponent (applyJoinEvents events links) firstNode secondNode = true
  | [], _, _, _, _, membership => by cases membership
  | (headFirst, headSecond) :: restEvents, links, forest, firstNode, secondNode,
      membership => by
      cases membership with
      | head =>
          exact isSameComponent_applyJoinEvents_ofBase restEvents _
            (isUnionFindForest_unionFindJoin links _ _ forest) _ _
            (isSameComponent_unionFindJoin_joined links forest _ _)
      | tail _ tailMembership =>
          exact isSameComponent_applyJoinEvents_ofMem restEvents
            (unionFindJoin links headFirst headSecond)
            (isUnionFindForest_unionFindJoin links headFirst headSecond forest)
            firstNode secondNode tailMembership

/-- ★ **The universal property of the event fold** (elimination): anything the fold relates is
related by ANY view that contains the base view and relates every event pair of the trace — the
banked single-join `_lift`, folded.  This is what lets a whole trace be re-played in a different
order: membership decomposes event by event and re-assembles through the target's facts. -/
theorem isSameComponent_applyJoinEvents_lift :
    (events : List (Nat × Nat)) → (links target : List (Nat × Nat)) →
    isUnionFindForest links →
    (∀ nodeOne nodeTwo : Nat, isSameComponent links nodeOne nodeTwo = true →
      isSameComponent target nodeOne nodeTwo = true) →
    (∀ firstNode secondNode : Nat, (firstNode, secondNode) ∈ events →
      isSameComponent target firstNode secondNode = true) →
    (probeOne probeTwo : Nat) →
    isSameComponent (applyJoinEvents events links) probeOne probeTwo = true →
    isSameComponent target probeOne probeTwo = true
  | [], _, _, _, liftBase, _, probeOne, probeTwo, inFold => liftBase probeOne probeTwo inFold
  | (headFirst, headSecond) :: restEvents, links, target, forest, liftBase, joinedAll,
      probeOne, probeTwo, inFold =>
      isSameComponent_applyJoinEvents_lift restEvents
        (unionFindJoin links headFirst headSecond) target
        (isUnionFindForest_unionFindJoin links headFirst headSecond forest)
        (fun nodeOne nodeTwo inJoin => isSameComponent_unionFindJoin_lift links target forest
          headFirst headSecond liftBase
          (joinedAll headFirst headSecond (List.Mem.head restEvents))
          nodeOne nodeTwo inJoin)
        (fun firstNode secondNode memRest => joinedAll firstNode secondNode
          (List.Mem.tail (headFirst, headSecond) memRest))
        probeOne probeTwo inFold

/-! ## The view exchange -/

/-- ★ **The component view of a fold depends only on the MEMBERSHIP of its trace** — any two
mem-equivalent event lists (in particular, any reordering) produce pointwise-equal views.  Double
elimination: each fold lifts into the other via the universal property, with completeness supplying
the joined-pair facts through the membership translation. -/
theorem componentView_applyJoinEvents_ofMemEquiv
    (eventsOne eventsTwo : List (Nat × Nat)) (links : List (Nat × Nat))
    (forest : isUnionFindForest links)
    (memForward : ∀ firstNode secondNode : Nat,
      (firstNode, secondNode) ∈ eventsOne → (firstNode, secondNode) ∈ eventsTwo)
    (memBackward : ∀ firstNode secondNode : Nat,
      (firstNode, secondNode) ∈ eventsTwo → (firstNode, secondNode) ∈ eventsOne)
    (probeOne probeTwo : Nat) :
    isSameComponent (applyJoinEvents eventsOne links) probeOne probeTwo
      = isSameComponent (applyJoinEvents eventsTwo links) probeOne probeTwo := by
  apply boolEqOfImpliesBoth
  · intro inFoldOne
    exact isSameComponent_applyJoinEvents_lift eventsOne links
      (applyJoinEvents eventsTwo links) forest
      (fun nodeOne nodeTwo base => isSameComponent_applyJoinEvents_ofBase eventsTwo links
        forest nodeOne nodeTwo base)
      (fun firstNode secondNode memOne => isSameComponent_applyJoinEvents_ofMem eventsTwo
        links forest firstNode secondNode (memForward firstNode secondNode memOne))
      probeOne probeTwo inFoldOne
  · intro inFoldTwo
    exact isSameComponent_applyJoinEvents_lift eventsTwo links
      (applyJoinEvents eventsOne links) forest
      (fun nodeOne nodeTwo base => isSameComponent_applyJoinEvents_ofBase eventsOne links
        forest nodeOne nodeTwo base)
      (fun firstNode secondNode memTwo => isSameComponent_applyJoinEvents_ofMem eventsOne
        links forest firstNode secondNode (memBackward firstNode secondNode memTwo))
      probeOne probeTwo inFoldTwo

/-- ★ **The view-side block exchange** — transposing two trace blocks is invisible to the
partition (mem-equivalence of the two concatenations). -/
theorem componentView_applyJoinEvents_append_comm
    (firstBlock secondBlock : List (Nat × Nat)) (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (probeOne probeTwo : Nat) :
    isSameComponent (applyJoinEvents (firstBlock ++ secondBlock) links) probeOne probeTwo
      = isSameComponent (applyJoinEvents (secondBlock ++ firstBlock) links) probeOne probeTwo :=
  componentView_applyJoinEvents_ofMemEquiv (firstBlock ++ secondBlock)
    (secondBlock ++ firstBlock) links forest
    (fun firstNode secondNode membership => by
      cases pairMemAppendCases firstBlock secondBlock (firstNode, secondNode) membership with
      | inl inFirst =>
          exact pairMemAppendOfRight secondBlock firstBlock (firstNode, secondNode) inFirst
      | inr inSecond =>
          exact pairMemAppendOfLeft secondBlock firstBlock (firstNode, secondNode) inSecond)
    (fun firstNode secondNode membership => by
      cases pairMemAppendCases secondBlock firstBlock (firstNode, secondNode) membership with
      | inl inSecond =>
          exact pairMemAppendOfRight firstBlock secondBlock (firstNode, secondNode) inSecond
      | inr inFirst =>
          exact pairMemAppendOfLeft firstBlock secondBlock (firstNode, secondNode) inFirst)
    probeOne probeTwo

/-- Folding over a pre-joined base sees the same view as joining after the fold — the singleton
instance of mem-equivalence (`(pair) :: events` vs `events ++ [pair]`). -/
theorem componentView_applyJoinEvents_joinRight
    (events : List (Nat × Nat)) (links : List (Nat × Nat)) (forest : isUnionFindForest links)
    (firstNode secondNode probeOne probeTwo : Nat) :
    isSameComponent (applyJoinEvents events (unionFindJoin links firstNode secondNode))
        probeOne probeTwo
      = isSameComponent (unionFindJoin (applyJoinEvents events links) firstNode secondNode)
        probeOne probeTwo := by
  have listsEq : applyJoinEvents (events ++ [(firstNode, secondNode)]) links
      = unionFindJoin (applyJoinEvents events links) firstNode secondNode :=
    applyJoinEvents_append events [(firstNode, secondNode)] links
  rw [← listsEq]
  exact componentView_applyJoinEvents_ofMemEquiv ((firstNode, secondNode) :: events)
    (events ++ [(firstNode, secondNode)]) links forest
    (fun nodeOne nodeTwo membership => by
      cases membership with
      | head => exact pairMemAppendOfRight events _ _ (List.Mem.head [])
      | tail _ tailMembership =>
          exact pairMemAppendOfLeft events [(firstNode, secondNode)] _ tailMembership)
    (fun nodeOne nodeTwo membership => by
      cases pairMemAppendCases events [(firstNode, secondNode)] (nodeOne, nodeTwo)
          membership with
      | inl inEvents => exact List.Mem.tail (firstNode, secondNode) inEvents
      | inr inSingleton =>
          cases inSingleton with
          | head => exact List.Mem.head events
          | tail _ impossible => cases impossible)
    probeOne probeTwo

/-! ## The count exchange -/

/-- ★ **One event commutes past a whole trace, count-wise**: pre-joining a pair costs the same loop
total as post-testing it after the trace.  The inductive step is the banked two-cap increment
exchange (`sameComponentIncrement_unionFindJoin_swap`), with the trailing counts reconciled by the
banked two-join view swap through the count congruence. -/
theorem countJoinEventLoops_singleJoinExchange :
    (events : List (Nat × Nat)) → (links : List (Nat × Nat)) → isUnionFindForest links →
    (firstNode secondNode : Nat) →
    (isSameComponent links firstNode secondNode).toNat
        + countJoinEventLoops events (unionFindJoin links firstNode secondNode)
      = countJoinEventLoops events links
          + (isSameComponent (applyJoinEvents events links) firstNode secondNode).toNat
  | [], links, _, firstNode, secondNode => by
      show (isSameComponent links firstNode secondNode).toNat + 0
          = 0 + (isSameComponent links firstNode secondNode).toNat
      rw [Nat.add_zero, Nat.zero_add]
  | (headFirst, headSecond) :: restEvents, links, forest, firstNode, secondNode => by
      have incrementSwap := sameComponentIncrement_unionFindJoin_swap links forest
        firstNode secondNode headFirst headSecond
      have countsEq : countJoinEventLoops restEvents
            (unionFindJoin (unionFindJoin links firstNode secondNode) headFirst headSecond)
          = countJoinEventLoops restEvents
            (unionFindJoin (unionFindJoin links headFirst headSecond) firstNode secondNode) :=
        countJoinEventLoops_congr restEvents _ _
          (isUnionFindForest_unionFindJoin _ headFirst headSecond
            (isUnionFindForest_unionFindJoin links firstNode secondNode forest))
          (isUnionFindForest_unionFindJoin _ firstNode secondNode
            (isUnionFindForest_unionFindJoin links headFirst headSecond forest))
          (fun probeOne probeTwo => isSameComponent_unionFindJoin_swap links forest
            firstNode secondNode headFirst headSecond probeOne probeTwo)
      have recursiveExchange := countJoinEventLoops_singleJoinExchange restEvents
        (unionFindJoin links headFirst headSecond)
        (isUnionFindForest_unionFindJoin links headFirst headSecond forest)
        firstNode secondNode
      show (isSameComponent links firstNode secondNode).toNat
            + ((isSameComponent (unionFindJoin links firstNode secondNode)
                  headFirst headSecond).toNat
                + countJoinEventLoops restEvents
                    (unionFindJoin (unionFindJoin links firstNode secondNode)
                      headFirst headSecond))
          = ((isSameComponent links headFirst headSecond).toNat
                + countJoinEventLoops restEvents (unionFindJoin links headFirst headSecond))
              + (isSameComponent
                  (applyJoinEvents restEvents (unionFindJoin links headFirst headSecond))
                  firstNode secondNode).toNat
      rw [← Nat.add_assoc, incrementSwap, countsEq, Nat.add_assoc, recursiveExchange,
        ← Nat.add_assoc]

/-- The cross-exchange of two whole blocks: each block's count over the other's output equals the
transposed reading.  Peels the first block; each event commutes past the second block by
`countJoinEventLoops_singleJoinExchange`, with the fold-vs-join base reconciled through the count
congruence over `componentView_applyJoinEvents_joinRight`. -/
theorem countJoinEventLoops_crossExchange :
    (firstBlock : List (Nat × Nat)) → (secondBlock : List (Nat × Nat)) →
    (links : List (Nat × Nat)) → isUnionFindForest links →
    countJoinEventLoops firstBlock links
        + countJoinEventLoops secondBlock (applyJoinEvents firstBlock links)
      = countJoinEventLoops secondBlock links
          + countJoinEventLoops firstBlock (applyJoinEvents secondBlock links)
  | [], secondBlock, links, _ => by
      show 0 + countJoinEventLoops secondBlock links
          = countJoinEventLoops secondBlock links + 0
      rw [Nat.zero_add, Nat.add_zero]
  | (headFirst, headSecond) :: restEvents, secondBlock, links, forest => by
      have crossRest := countJoinEventLoops_crossExchange restEvents secondBlock
        (unionFindJoin links headFirst headSecond)
        (isUnionFindForest_unionFindJoin links headFirst headSecond forest)
      have singleExchange := countJoinEventLoops_singleJoinExchange secondBlock links forest
        headFirst headSecond
      have countsEq : countJoinEventLoops restEvents
            (applyJoinEvents secondBlock (unionFindJoin links headFirst headSecond))
          = countJoinEventLoops restEvents
            (unionFindJoin (applyJoinEvents secondBlock links) headFirst headSecond) :=
        countJoinEventLoops_congr restEvents _ _
          (isUnionFindForest_applyJoinEvents secondBlock _
            (isUnionFindForest_unionFindJoin links headFirst headSecond forest))
          (isUnionFindForest_unionFindJoin _ headFirst headSecond
            (isUnionFindForest_applyJoinEvents secondBlock links forest))
          (fun probeOne probeTwo => componentView_applyJoinEvents_joinRight secondBlock links
            forest headFirst headSecond probeOne probeTwo)
      show ((isSameComponent links headFirst headSecond).toNat
            + countJoinEventLoops restEvents (unionFindJoin links headFirst headSecond))
            + countJoinEventLoops secondBlock
                (applyJoinEvents restEvents (unionFindJoin links headFirst headSecond))
          = countJoinEventLoops secondBlock links
              + ((isSameComponent (applyJoinEvents secondBlock links)
                    headFirst headSecond).toNat
                  + countJoinEventLoops restEvents
                      (unionFindJoin (applyJoinEvents secondBlock links)
                        headFirst headSecond))
      rw [Nat.add_assoc, crossRest, ← Nat.add_assoc, singleExchange, countsEq,
        Nat.add_assoc]

/-- ★ **The count-side block exchange** — the loop total of a trace is invariant under transposing
its two blocks.  Split both concatenations (`countJoinEventLoops_append`) and cross-exchange. -/
theorem countJoinEventLoops_append_comm
    (firstBlock secondBlock : List (Nat × Nat)) (links : List (Nat × Nat))
    (forest : isUnionFindForest links) :
    countJoinEventLoops (firstBlock ++ secondBlock) links
      = countJoinEventLoops (secondBlock ++ firstBlock) links := by
  rw [countJoinEventLoops_append firstBlock secondBlock links,
    countJoinEventLoops_append secondBlock firstBlock links]
  exact countJoinEventLoops_crossExchange firstBlock secondBlock links forest

/-! ## Honesty marker -/

/-- **Honesty marker — the block exchange of join-event traces is PROVED, view and count.**  The
component view of an event fold depends only on trace membership
(`componentView_applyJoinEvents_ofMemEquiv`, via the list-level universal property
`isSameComponent_applyJoinEvents_lift` with `_ofBase`/`_ofMem`), so any block transposition is
invisible (`componentView_applyJoinEvents_append_comm`); the loop count — where multiplicity
matters and membership is too weak — is block-swap invariant by the cross-exchange double
induction over the banked two-cap increment exchange and two-join view swap
(`countJoinEventLoops_append_comm`).  NOT yet covered: the cross-order trace CORRESPONDENCE (that
the two Godement orders' traces are a `blockRotate` rename + block swap of each other — the wire-
side event congruence over the shipped window machinery), and the final `MatchingComponentSim`
bundling.  `= true`. -/
def fxMode_hasMatchingJoinEventBlockExchange : Bool := true

end FX1Poly.Polygraph
