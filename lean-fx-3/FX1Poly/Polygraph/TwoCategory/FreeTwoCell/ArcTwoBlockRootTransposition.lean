import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointCapMixedSwapSimCount

/-! # MODE-COMMUTE r27 — the UNIFORM two-block root-transposition engine (BRICK X, general form)

## What this ships

r26 named ONE missing lemma as the sole obstruction to the general cap/mixed disjoint atom-swap
`ArcStepSimCount` arms (and hence to the whole-cell fold): *root-level disjoint-support 2-join-block
commutation* — for two join-blocks acting on disjoint node-and-root supports, `unionFindRootOf` is
order-independent up to the fresh-block `sigma`.  r26 verified it only on concrete supports by `decide`;
the general theorem was the r27 bill ("BRICK X").

This file BUILDS that engine, uniformly for ALL atom pairs.  The key structural observation: both the cup
and the cap update their links by the SAME shape — `twoJoinBlock links u v e = unionFindJoin (unionFindJoin
links u v) e u` (cup: `u,v,e` = the three fresh ids; cap: `u,v` = the two read wires, `e` = the fresh
event).  So ONE closed form covers every arm:

  ★ `rootOf_twoJoinBlock` — the CLOSED FORM of a block's root map over a forest:
    `rootOf (twoJoinBlock L u v e) t = if RU == R t || e == R t then RV else R t`
    (`RU`/`RV` the pre-join roots of `u`/`v`; the event's own root is itself and differs from `RU`).
    Notably the loop case `RU = RV` is INCLUDED — no distinctness of the two read roots is needed.
  ★ `rootOf_twoBlocks_flat` — the closed form through TWO stacked blocks, flattened:
    `if G1 then RV1 else if G2 then RV2 else R t`, under the ten support-disjointness disequalities.
  ★ `twoBlocksSigma_rootComm` — ★★ THE ENGINE ★★: for two blocks whose supports satisfy the ten
    disequalities, the two firing orders are root-conjugate under any window permutation `sigma`
    (injective, fixing everything below the fresh base, preserving the at-or-above zone):
    `rootOf (sigma-blocks in SWAPPED order) (sigma x) = sigma (rootOf (blocks in order) x)`.
    Both sides collapse to their flat forms; the guards transport along `sigma` (`beq_congr_inj`); the
    outer-if transposition is exactly the guard-disjointness (`flatIfPair_transpose`).

## The honest sharpening (machine-forced, strictly finer than r26's guard)

The engine needs only TEN disequalities — and `RV1 != RV2` is NOT among them: two caps whose windows are
disjoint may share the component of their SECOND reads (the two merges then point into the same target
root, which commutes).  r26's honest guard "component-disjoint reads" is SUFFICIENT but not necessary;
the sharp guard excludes only first-read/first-read, first-read/other-window and event collisions.  The
r26 negative control (roots `83` vs `81`) violates exactly `rootOneFirst != rootTwoFirst`.

## Supporting bricks

  * `unionFindRootOf_of_unmentioned` — an id at-or-above the mention bound is its own root;
  * `rootComm_of_windowPermutation` — the BASE conjugation: a permutation fixing everything below the
    bound and preserving the at-or-above zone is a root automorphism of any below-bound forest;
  * `blockRotate_preservesAtOrAboveBase` — the r17 window rotation satisfies that zone preservation;
  * `rootOf_twoJoinBlock_untouched` / `isSameComponent_twoJoinBlock_untouched` — the locality
    corollaries the loop-count and read-preservation legs of the r27 arms consume.

The r27 general atom arms (`ArcDisjointAtomSwapGeneralArms`) consume this engine; the pins stay `false`
here (this file is machinery — the arms and the whole-cell fold are the deliveries).

Raw Lean 4 + Init; every proof is `rw`-algebra over the shipped `unionFindRootOf_unionFindJoin` +
structural `Bool` case analysis.  No `omega`, no `WellFounded.fix`, no wildcard matches on open scrutinees.
Per-declaration `#assert_no_axioms` + independent `#print axioms` in the twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Locality bricks -/

/-- An id at-or-above the mention bound of a link list is parentless, hence its own root.  The
`unionFindParent_none_of_lt` + `unionFindRootOf_of_parentless` composition the engine reads fresh-id
roots off with. -/
theorem unionFindRootOf_of_unmentioned (links : List (Nat × Nat)) (bound : Nat)
    (childrenBelow : ∀ edge ∈ links, edge.1 < bound) (node : Nat) (isAtOrAbove : bound ≤ node) :
    unionFindRootOf links node = node :=
  unionFindRootOf_of_parentless links node
    (unionFindParent_none_of_lt bound links childrenBelow node isAtOrAbove)

/-- The block rotation preserves the at-or-above-base zone: an id at or above `lo` lands at or above
`lo` (first block shifts up, second block lands back inside the window, the tail is fixed).  The zone
fact `rootComm_of_windowPermutation` needs of its `sigma`. -/
theorem blockRotate_preservesAtOrAboveBase (lo w1 w2 x : Nat) (isAtOrAbove : lo ≤ x) :
    lo ≤ blockRotate lo w1 w2 x := by
  cases Nat.lt_or_ge x (lo + w1) with
  | inl inFirstBlock =>
      rw [blockRotate_firstBlock lo w1 w2 x isAtOrAbove inFirstBlock]
      exact Nat.le_trans isAtOrAbove (Nat.le_add_right x w2)
  | inr atLeastMid =>
      cases Nat.lt_or_ge x (lo + w1 + w2) with
      | inl inSecondBlock =>
          rw [blockRotate_secondBlock lo w1 w2 x atLeastMid inSecondBlock]
          have widthBelow : w1 ≤ x := Nat.le_trans (Nat.le_add_left w1 lo) atLeastMid
          exact Nat.not_lt.mp (fun isBelow => by
            have shifted : (x - w1) + w1 < lo + w1 := Nat.add_lt_add_right isBelow w1
            rw [subAddCancel w1 x widthBelow] at shifted
            exact absurd shifted (Nat.not_lt.mpr atLeastMid))
      | inr aboveWindow =>
          rw [blockRotate_above lo w1 w2 x aboveWindow]
          exact isAtOrAbove

/-- ★ **The base root conjugation.**  A permutation `sigma` fixing every id below `bound` and mapping
the at-or-above zone into itself is a `unionFindRootOf` automorphism of any link list whose endpoints
all lie below `bound`: below the bound both sides are fixed (and roots stay below the bound); at or
above it both sides are their own (unmentioned) roots. -/
theorem rootComm_of_windowPermutation (links : List (Nat × Nat)) (bound : Nat)
    (endpointsBelow : ∀ edge ∈ links, edge.1 < bound ∧ edge.2 < bound)
    (sigma : Nat → Nat)
    (fixesBelow : ∀ node, node < bound → sigma node = node)
    (preservesAtOrAbove : ∀ node, bound ≤ node → bound ≤ sigma node) :
    ∀ x, unionFindRootOf links (sigma x) = sigma (unionFindRootOf links x) := by
  intro x
  have childrenBelow : ∀ edge ∈ links, edge.1 < bound := fun edge he => (endpointsBelow edge he).1
  have parentsBelow : ∀ edge ∈ links, edge.2 < bound := fun edge he => (endpointsBelow edge he).2
  cases Nat.lt_or_ge x bound with
  | inl isBelow =>
      rw [fixesBelow x isBelow,
        fixesBelow (unionFindRootOf links x) (unionFindRootOf_lt_of_fresh links bound parentsBelow x isBelow)]
  | inr isAtOrAbove =>
      rw [unionFindRootOf_of_unmentioned links bound childrenBelow x isAtOrAbove,
        unionFindRootOf_of_unmentioned links bound childrenBelow (sigma x) (preservesAtOrAbove x isAtOrAbove)]

/-! ## The uniform block shape -/

/-- ★ **The uniform two-join block** — the SINGLE links-update shape shared by the cup and the cap:
join the two carrier nodes, then join the fresh event onto the first carrier.  Cup: `u,v,e` are the
three fresh ids (`nf, nf+1, nf+2`); cap: `u,v` are the two read wires and `e` the fresh event `nf`. -/
def twoJoinBlock (links : List (Nat × Nat)) (firstCarrier secondCarrier eventNode : Nat) :
    List (Nat × Nat) :=
  unionFindJoin (unionFindJoin links firstCarrier secondCarrier) eventNode firstCarrier

/-- A CUP's link update IS a `twoJoinBlock` on the three fresh ids.  Definitional. -/
theorem stepCupArc_links_twoJoinBlock (state : ArcWireState) (position : Nat) :
    (stepCupArc state position).links
      = twoJoinBlock state.links state.nextFresh (state.nextFresh + 1) (state.nextFresh + 2) := rfl

/-- A CAP's link update IS a `twoJoinBlock` on the two read wires and the fresh event.  Definitional. -/
theorem stepCapArc_links_twoJoinBlock (state : ArcWireState) (position : Nat) :
    (stepCapArc state position).links
      = twoJoinBlock state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)) state.nextFresh := rfl

/-- A `twoJoinBlock` preserves the forest invariant (two nested join preservations). -/
theorem isUnionFindForest_twoJoinBlock (links : List (Nat × Nat))
    (firstCarrier secondCarrier eventNode : Nat) (forest : isUnionFindForest links) :
    isUnionFindForest (twoJoinBlock links firstCarrier secondCarrier eventNode) :=
  isUnionFindForest_unionFindJoin _ _ _ (isUnionFindForest_unionFindJoin _ _ _ forest)

/-! ## The closed form of one block's root map -/

/-- ★ **The closed form of a block's root map over a forest.**  With `firstRoot`/`secondRoot` the
pre-join roots of the two carriers and the event its own root distinct from `firstRoot`:

  `rootOf (twoJoinBlock L u v e) t  =  if firstRoot == R t || e == R t then secondRoot else R t`.

The loop case `firstRoot = secondRoot` is INCLUDED (the wire join is then a no-op and the guard's
true-branch is the unchanged root); no distinctness between the carrier roots is required. -/
theorem rootOf_twoJoinBlock (links : List (Nat × Nat)) (forest : isUnionFindForest links)
    (firstCarrier secondCarrier eventNode firstRoot secondRoot : Nat)
    (hFirstRoot : unionFindRootOf links firstCarrier = firstRoot)
    (hSecondRoot : unionFindRootOf links secondCarrier = secondRoot)
    (hEventOwnRoot : unionFindRootOf links eventNode = eventNode)
    (hEventNeFirstRoot : eventNode ≠ firstRoot) :
    ∀ probe, unionFindRootOf (twoJoinBlock links firstCarrier secondCarrier eventNode) probe
      = if firstRoot == unionFindRootOf links probe || eventNode == unionFindRootOf links probe
        then secondRoot else unionFindRootOf links probe := by
  intro probe
  have forestInner : isUnionFindForest (unionFindJoin links firstCarrier secondCarrier) :=
    isUnionFindForest_unionFindJoin links firstCarrier secondCarrier forest
  have innerAt : ∀ t, unionFindRootOf (unionFindJoin links firstCarrier secondCarrier) t
      = if firstRoot == unionFindRootOf links t then secondRoot else unionFindRootOf links t := by
    intro t
    rw [unionFindRootOf_unionFindJoin links firstCarrier secondCarrier t forest, hFirstRoot, hSecondRoot]
  have innerEventRoot : unionFindRootOf (unionFindJoin links firstCarrier secondCarrier) eventNode
      = eventNode := by
    rw [innerAt eventNode, hEventOwnRoot, natBeqFalseOfNe (fun h => hEventNeFirstRoot h.symm)]
    rfl
  have innerFirstRoot : unionFindRootOf (unionFindJoin links firstCarrier secondCarrier) firstCarrier
      = secondRoot := by
    rw [innerAt firstCarrier, hFirstRoot, natBeqSelf]
    rfl
  show unionFindRootOf
      (unionFindJoin (unionFindJoin links firstCarrier secondCarrier) eventNode firstCarrier) probe = _
  rw [unionFindRootOf_unionFindJoin (unionFindJoin links firstCarrier secondCarrier) eventNode
      firstCarrier probe forestInner, innerEventRoot, innerFirstRoot, innerAt probe]
  cases hFirstGuard : firstRoot == unionFindRootOf links probe with
  | true =>
      show (if eventNode == secondRoot then secondRoot else secondRoot) = secondRoot
      cases eventNode == secondRoot with
      | true => rfl
      | false => rfl
  | false => rfl

/-- ★ **Block locality** — a probe whose root collides with neither the block's first-carrier root nor
its event keeps its root through the block.  The lever the loop-guard and read-preservation legs of the
disjoint arms consume. -/
theorem rootOf_twoJoinBlock_untouched (links : List (Nat × Nat)) (forest : isUnionFindForest links)
    (firstCarrier secondCarrier eventNode firstRoot secondRoot : Nat)
    (hFirstRoot : unionFindRootOf links firstCarrier = firstRoot)
    (hSecondRoot : unionFindRootOf links secondCarrier = secondRoot)
    (hEventOwnRoot : unionFindRootOf links eventNode = eventNode)
    (hEventNeFirstRoot : eventNode ≠ firstRoot)
    (probe : Nat)
    (hFirstUntouched : firstRoot ≠ unionFindRootOf links probe)
    (hEventUntouched : eventNode ≠ unionFindRootOf links probe) :
    unionFindRootOf (twoJoinBlock links firstCarrier secondCarrier eventNode) probe
      = unionFindRootOf links probe := by
  rw [rootOf_twoJoinBlock links forest firstCarrier secondCarrier eventNode firstRoot secondRoot
      hFirstRoot hSecondRoot hEventOwnRoot hEventNeFirstRoot probe,
    natBeqFalseOfNe hFirstUntouched, natBeqFalseOfNe hEventUntouched]
  rfl

/-- ★ **Same-component locality** — a block leaves the same-component relation of two untouched probes
unchanged (both probes' roots survive the block, so the `==` of roots is byte-stable). -/
theorem isSameComponent_twoJoinBlock_untouched (links : List (Nat × Nat))
    (forest : isUnionFindForest links)
    (firstCarrier secondCarrier eventNode firstRoot secondRoot : Nat)
    (hFirstRoot : unionFindRootOf links firstCarrier = firstRoot)
    (hSecondRoot : unionFindRootOf links secondCarrier = secondRoot)
    (hEventOwnRoot : unionFindRootOf links eventNode = eventNode)
    (hEventNeFirstRoot : eventNode ≠ firstRoot)
    (leftProbe rightProbe : Nat)
    (hLeftFirstUntouched : firstRoot ≠ unionFindRootOf links leftProbe)
    (hLeftEventUntouched : eventNode ≠ unionFindRootOf links leftProbe)
    (hRightFirstUntouched : firstRoot ≠ unionFindRootOf links rightProbe)
    (hRightEventUntouched : eventNode ≠ unionFindRootOf links rightProbe) :
    isSameComponent (twoJoinBlock links firstCarrier secondCarrier eventNode) leftProbe rightProbe
      = isSameComponent links leftProbe rightProbe := by
  show (unionFindRootOf (twoJoinBlock links firstCarrier secondCarrier eventNode) leftProbe
      == unionFindRootOf (twoJoinBlock links firstCarrier secondCarrier eventNode) rightProbe)
    = (unionFindRootOf links leftProbe == unionFindRootOf links rightProbe)
  rw [rootOf_twoJoinBlock_untouched links forest firstCarrier secondCarrier eventNode firstRoot
      secondRoot hFirstRoot hSecondRoot hEventOwnRoot hEventNeFirstRoot leftProbe
      hLeftFirstUntouched hLeftEventUntouched,
    rootOf_twoJoinBlock_untouched links forest firstCarrier secondCarrier eventNode firstRoot
      secondRoot hFirstRoot hSecondRoot hEventOwnRoot hEventNeFirstRoot rightProbe
      hRightFirstUntouched hRightEventUntouched]

/-! ## The flat closed form through two stacked blocks -/

/-- ★ **The flat closed form through two stacked blocks.**  Firing block one then block two over a
forest, the composite root map flattens to a two-guard dispatch — PROVIDED the ten support
disequalities hold (each guard's support avoids the other block's carriers, events, and merge target;
the two blocks' merge targets `RV1`/`RV2` may coincide — that disequality is NOT needed). -/
theorem rootOf_twoBlocks_flat (links : List (Nat × Nat)) (forest : isUnionFindForest links)
    (readOneFirst readOneSecond eventOne readTwoFirst readTwoSecond eventTwo : Nat)
    (rootOneFirst rootOneSecond rootTwoFirst rootTwoSecond : Nat)
    (hRootOneFirst : unionFindRootOf links readOneFirst = rootOneFirst)
    (hRootOneSecond : unionFindRootOf links readOneSecond = rootOneSecond)
    (hRootTwoFirst : unionFindRootOf links readTwoFirst = rootTwoFirst)
    (hRootTwoSecond : unionFindRootOf links readTwoSecond = rootTwoSecond)
    (hEventOneRoot : unionFindRootOf links eventOne = eventOne)
    (hEventTwoRoot : unionFindRootOf links eventTwo = eventTwo)
    (dEventOneRootOne : eventOne ≠ rootOneFirst)
    (dRootRoot : rootOneFirst ≠ rootTwoFirst)
    (dEventOneRootTwo : eventOne ≠ rootTwoFirst)
    (dRootOneTargetTwo : rootOneFirst ≠ rootTwoSecond)
    (dEventOneTargetTwo : eventOne ≠ rootTwoSecond)
    (dRootOneEventTwo : rootOneFirst ≠ eventTwo)
    (dEventEvent : eventOne ≠ eventTwo)
    (dEventTwoRootTwo : eventTwo ≠ rootTwoFirst)
    (dRootTwoTargetOne : rootTwoFirst ≠ rootOneSecond)
    (dEventTwoTargetOne : eventTwo ≠ rootOneSecond) :
    ∀ probe, unionFindRootOf
        (twoJoinBlock (twoJoinBlock links readOneFirst readOneSecond eventOne)
          readTwoFirst readTwoSecond eventTwo) probe
      = if rootOneFirst == unionFindRootOf links probe || eventOne == unionFindRootOf links probe
        then rootOneSecond
        else if rootTwoFirst == unionFindRootOf links probe || eventTwo == unionFindRootOf links probe
        then rootTwoSecond
        else unionFindRootOf links probe := by
  have forestOne : isUnionFindForest (twoJoinBlock links readOneFirst readOneSecond eventOne) :=
    isUnionFindForest_twoJoinBlock links readOneFirst readOneSecond eventOne forest
  have innerAt := rootOf_twoJoinBlock links forest readOneFirst readOneSecond eventOne
    rootOneFirst rootOneSecond hRootOneFirst hRootOneSecond hEventOneRoot dEventOneRootOne
  have blockOneRootTwoFirst : unionFindRootOf (twoJoinBlock links readOneFirst readOneSecond eventOne)
      readTwoFirst = rootTwoFirst := by
    rw [innerAt readTwoFirst, hRootTwoFirst, natBeqFalseOfNe dRootRoot,
      natBeqFalseOfNe dEventOneRootTwo]
    rfl
  have blockOneRootTwoSecond : unionFindRootOf (twoJoinBlock links readOneFirst readOneSecond eventOne)
      readTwoSecond = rootTwoSecond := by
    rw [innerAt readTwoSecond, hRootTwoSecond, natBeqFalseOfNe dRootOneTargetTwo,
      natBeqFalseOfNe dEventOneTargetTwo]
    rfl
  have blockOneEventTwo : unionFindRootOf (twoJoinBlock links readOneFirst readOneSecond eventOne)
      eventTwo = eventTwo := by
    rw [innerAt eventTwo, hEventTwoRoot, natBeqFalseOfNe dRootOneEventTwo,
      natBeqFalseOfNe dEventEvent]
    rfl
  have outerAt := rootOf_twoJoinBlock (twoJoinBlock links readOneFirst readOneSecond eventOne)
    forestOne readTwoFirst readTwoSecond eventTwo rootTwoFirst rootTwoSecond
    blockOneRootTwoFirst blockOneRootTwoSecond blockOneEventTwo dEventTwoRootTwo
  intro probe
  rw [outerAt probe, innerAt probe]
  cases hGuardOne : rootOneFirst == unionFindRootOf links probe with
  | true =>
      show (if rootTwoFirst == rootOneSecond || eventTwo == rootOneSecond
            then rootTwoSecond else rootOneSecond) = rootOneSecond
      rw [natBeqFalseOfNe dRootTwoTargetOne, natBeqFalseOfNe dEventTwoTargetOne]
      rfl
  | false =>
      cases hGuardEvent : eventOne == unionFindRootOf links probe with
      | true =>
          show (if rootTwoFirst == rootOneSecond || eventTwo == rootOneSecond
                then rootTwoSecond else rootOneSecond) = rootOneSecond
          rw [natBeqFalseOfNe dRootTwoTargetOne, natBeqFalseOfNe dEventTwoTargetOne]
          rfl
      | false => rfl

/-! ## The guarded-if transposition (pure Bool combinatorics) -/

/-- The two-guard dispatch transposes when the two guard supports are disjoint (the four cross
disequalities).  Sixteen-way structural `Bool` case analysis; the double-hit branches are refuted by
the cross disequalities. -/
theorem flatIfPair_transpose (rootOne eventOne valueOne rootTwo eventTwo valueTwo
    probeRoot fallback : Nat)
    (dRootRoot : rootOne ≠ rootTwo) (dRootEvent : rootOne ≠ eventTwo)
    (dEventRoot : eventOne ≠ rootTwo) (dEventEvent : eventOne ≠ eventTwo) :
    (if rootTwo == probeRoot || eventTwo == probeRoot then valueTwo
      else if rootOne == probeRoot || eventOne == probeRoot then valueOne else fallback)
    = (if rootOne == probeRoot || eventOne == probeRoot then valueOne
      else if rootTwo == probeRoot || eventTwo == probeRoot then valueTwo else fallback) := by
  cases hOne : rootOne == probeRoot with
  | true =>
      have rootOneHits : rootOne = probeRoot := of_decide_eq_true hOne
      rw [natBeqFalseOfNe (fun hTwo => dRootRoot (rootOneHits.trans hTwo.symm)),
        natBeqFalseOfNe (fun hTwo => dRootEvent (rootOneHits.trans hTwo.symm))]
      rfl
  | false =>
      cases hEvent : eventOne == probeRoot with
      | true =>
          have eventOneHits : eventOne = probeRoot := of_decide_eq_true hEvent
          rw [natBeqFalseOfNe (fun hTwo => dEventRoot (eventOneHits.trans hTwo.symm)),
            natBeqFalseOfNe (fun hTwo => dEventEvent (eventOneHits.trans hTwo.symm))]
          rfl
      | false => rfl

/-! ## ★★ THE ENGINE — the sigma-twisted two-block transposition ★★ -/

/-- ★★ **BRICK X, general form — the root-level disjoint two-block transposition under the window
permutation.**  Over a below-`bound` forest, two `twoJoinBlock`s whose supports satisfy the ten
disequalities, fired in the two orders (the second order carrying the `sigma`-imaged supports — the
opposite fresh allocation), are root-CONJUGATE under any `sigma` that is injective, fixes everything
below `bound`, and preserves the at-or-above zone:

  `rootOf (sigma-block-two then sigma-block-one) (sigma x) = sigma (rootOf (block-one then block-two) x)`.

Both sides collapse to their flat closed forms; the base conjugation transports the probe root; the
guards transport along `sigma` by injectivity; and the final outer-if transposition is exactly the
support disjointness.  This is the lemma r26 named as the sole missing general brick — now
UNCONDITIONAL on the concrete support (no `decide`, no bounded node set). -/
theorem twoBlocksSigma_rootComm (links : List (Nat × Nat)) (forest : isUnionFindForest links)
    (bound : Nat) (endpointsBelow : ∀ edge ∈ links, edge.1 < bound ∧ edge.2 < bound)
    (sigma : Nat → Nat)
    (isInjective : ∀ firstId secondId, sigma firstId = sigma secondId → firstId = secondId)
    (fixesBelow : ∀ node, node < bound → sigma node = node)
    (preservesAtOrAbove : ∀ node, bound ≤ node → bound ≤ sigma node)
    (readOneFirst readOneSecond eventOne readTwoFirst readTwoSecond eventTwo : Nat)
    (rootOneFirst rootOneSecond rootTwoFirst rootTwoSecond : Nat)
    (hRootOneFirst : unionFindRootOf links readOneFirst = rootOneFirst)
    (hRootOneSecond : unionFindRootOf links readOneSecond = rootOneSecond)
    (hRootTwoFirst : unionFindRootOf links readTwoFirst = rootTwoFirst)
    (hRootTwoSecond : unionFindRootOf links readTwoSecond = rootTwoSecond)
    (hEventOneRoot : unionFindRootOf links eventOne = eventOne)
    (hEventTwoRoot : unionFindRootOf links eventTwo = eventTwo)
    (dEventOneRootOne : eventOne ≠ rootOneFirst)
    (dRootRoot : rootOneFirst ≠ rootTwoFirst)
    (dEventOneRootTwo : eventOne ≠ rootTwoFirst)
    (dRootOneTargetTwo : rootOneFirst ≠ rootTwoSecond)
    (dEventOneTargetTwo : eventOne ≠ rootTwoSecond)
    (dRootOneEventTwo : rootOneFirst ≠ eventTwo)
    (dEventEvent : eventOne ≠ eventTwo)
    (dEventTwoRootTwo : eventTwo ≠ rootTwoFirst)
    (dRootTwoTargetOne : rootTwoFirst ≠ rootOneSecond)
    (dEventTwoTargetOne : eventTwo ≠ rootOneSecond) :
    ∀ x, unionFindRootOf
        (twoJoinBlock (twoJoinBlock links (sigma readTwoFirst) (sigma readTwoSecond) (sigma eventTwo))
          (sigma readOneFirst) (sigma readOneSecond) (sigma eventOne)) (sigma x)
      = sigma (unionFindRootOf
          (twoJoinBlock (twoJoinBlock links readOneFirst readOneSecond eventOne)
            readTwoFirst readTwoSecond eventTwo) x) := by
  have base := rootComm_of_windowPermutation links bound endpointsBelow sigma fixesBelow
    preservesAtOrAbove
  have hSigmaRootOneFirst : unionFindRootOf links (sigma readOneFirst) = sigma rootOneFirst := by
    rw [base readOneFirst, hRootOneFirst]
  have hSigmaRootOneSecond : unionFindRootOf links (sigma readOneSecond) = sigma rootOneSecond := by
    rw [base readOneSecond, hRootOneSecond]
  have hSigmaRootTwoFirst : unionFindRootOf links (sigma readTwoFirst) = sigma rootTwoFirst := by
    rw [base readTwoFirst, hRootTwoFirst]
  have hSigmaRootTwoSecond : unionFindRootOf links (sigma readTwoSecond) = sigma rootTwoSecond := by
    rw [base readTwoSecond, hRootTwoSecond]
  have hSigmaEventOneRoot : unionFindRootOf links (sigma eventOne) = sigma eventOne := by
    rw [base eventOne, hEventOneRoot]
  have hSigmaEventTwoRoot : unionFindRootOf links (sigma eventTwo) = sigma eventTwo := by
    rw [base eventTwo, hEventTwoRoot]
  have flatA := rootOf_twoBlocks_flat links forest readOneFirst readOneSecond eventOne
    readTwoFirst readTwoSecond eventTwo rootOneFirst rootOneSecond rootTwoFirst rootTwoSecond
    hRootOneFirst hRootOneSecond hRootTwoFirst hRootTwoSecond hEventOneRoot hEventTwoRoot
    dEventOneRootOne dRootRoot dEventOneRootTwo dRootOneTargetTwo dEventOneTargetTwo
    dRootOneEventTwo dEventEvent dEventTwoRootTwo dRootTwoTargetOne dEventTwoTargetOne
  have flatB := rootOf_twoBlocks_flat links forest (sigma readTwoFirst) (sigma readTwoSecond)
    (sigma eventTwo) (sigma readOneFirst) (sigma readOneSecond) (sigma eventOne)
    (sigma rootTwoFirst) (sigma rootTwoSecond) (sigma rootOneFirst) (sigma rootOneSecond)
    hSigmaRootTwoFirst hSigmaRootTwoSecond hSigmaRootOneFirst hSigmaRootOneSecond
    hSigmaEventTwoRoot hSigmaEventOneRoot
    (fun h => dEventTwoRootTwo (isInjective _ _ h))
    (fun h => dRootRoot (isInjective _ _ h).symm)
    (fun h => dRootOneEventTwo (isInjective _ _ h).symm)
    (fun h => dRootTwoTargetOne (isInjective _ _ h))
    (fun h => dEventTwoTargetOne (isInjective _ _ h))
    (fun h => dEventOneRootTwo (isInjective _ _ h).symm)
    (fun h => dEventEvent (isInjective _ _ h).symm)
    (fun h => dEventOneRootOne (isInjective _ _ h))
    (fun h => dRootOneTargetTwo (isInjective _ _ h))
    (fun h => dEventOneTargetTwo (isInjective _ _ h))
  intro x
  rw [flatB (sigma x), flatA x, base x,
    beq_congr_inj sigma isInjective rootTwoFirst (unionFindRootOf links x),
    beq_congr_inj sigma isInjective eventTwo (unionFindRootOf links x),
    beq_congr_inj sigma isInjective rootOneFirst (unionFindRootOf links x),
    beq_congr_inj sigma isInjective eventOne (unionFindRootOf links x),
    ← ite_push_sigma sigma
      (rootOneFirst == unionFindRootOf links x || eventOne == unionFindRootOf links x)
      rootOneSecond
      (if rootTwoFirst == unionFindRootOf links x || eventTwo == unionFindRootOf links x
        then rootTwoSecond else unionFindRootOf links x),
    ← ite_push_sigma sigma
      (rootTwoFirst == unionFindRootOf links x || eventTwo == unionFindRootOf links x)
      rootTwoSecond (unionFindRootOf links x)]
  exact flatIfPair_transpose rootOneFirst eventOne (sigma rootOneSecond) rootTwoFirst eventTwo
    (sigma rootTwoSecond) (unionFindRootOf links x) (sigma (unionFindRootOf links x))
    dRootRoot dRootOneEventTwo dEventOneRootTwo dEventEvent

/-! ## Fire — the engine on the r26 cap x cap support, now WITHOUT `decide` on the sim fields -/

/-- The engine FIRED at the r26 disjoint cap x cap shape: seed forest `[(50,51),(52,53),(54,55)]`
(bound `56`), block one `(50,51,56)`, block two `(52,53,57)`, `sigma = blockRotate 56 1 1`.  The
firing instantiates every hypothesis with closed-value proofs — the universal conclusion holds for
EVERY probe, not a bounded support list (the advance over r26's `decide`-bounded fields). -/
theorem twoBlocksSigma_rootComm_capCapFire :
    ∀ x, unionFindRootOf
        (twoJoinBlock (twoJoinBlock [(50, 51), (52, 53), (54, 55)]
            (blockRotate 56 1 1 52) (blockRotate 56 1 1 53) (blockRotate 56 1 1 57))
          (blockRotate 56 1 1 50) (blockRotate 56 1 1 51) (blockRotate 56 1 1 56))
        (blockRotate 56 1 1 x)
      = blockRotate 56 1 1 (unionFindRootOf
          (twoJoinBlock (twoJoinBlock [(50, 51), (52, 53), (54, 55)] 50 51 56) 52 53 57) x) :=
  twoBlocksSigma_rootComm [(50, 51), (52, 53), (54, 55)] capCapDisjointSeed_isForest 56
    (by intro edge he; cases he with
      | head => exact ⟨by decide, by decide⟩
      | tail _ he2 => cases he2 with
        | head => exact ⟨by decide, by decide⟩
        | tail _ he3 => cases he3 with
          | head => exact ⟨by decide, by decide⟩
          | tail _ he4 => cases he4)
    (blockRotate 56 1 1) (blockRotate_inj 56 1 1)
    (fun node isBelow => blockRotate_fixesBelow 56 1 1 node isBelow)
    (fun node isAtOrAbove => blockRotate_preservesAtOrAboveBase 56 1 1 node isAtOrAbove)
    50 51 56 52 53 57 51 51 53 53
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-! ## Honesty marker + pins -/

/-- **Honesty marker — the uniform two-block root-transposition engine is SHIPPED, general form.**
The closed form of a block's root map (`rootOf_twoJoinBlock`, loop case included), its locality
corollaries, the flat two-block closed form under the ten support disequalities, and the
sigma-twisted transposition `twoBlocksSigma_rootComm` — r26's named BRICK X — all UNCONDITIONAL
(no bounded-support `decide`).  Sharpening: `rootOneSecond != rootTwoSecond` is NOT required — two
merges into a shared target commute; only first-read and event collisions obstruct.  `= true`. -/
def fxMode_hasTwoBlockRootTranspositionEngine : Bool := true

/-- **Honesty pin — the whole-cell disjoint whisker-support target stays OPEN here.**  This file is
the ENGINE; the general atom arms and the atom-to-cell double fold are its consumers.  `rfl`. -/
theorem arcTwoBlockRootTransposition_disjointWhiskerSupport_stays_false :
    fxMode_hasDisjointWhiskerSupport = false := rfl

/-- **Honesty pin — residual (2)'s renameable-level marker stays OPEN here.**  `rfl`. -/
theorem arcTwoBlockRootTransposition_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

/-- **Honesty pin — the machine-refuted same-partition-fresh keystone is NEVER flipped.**  `rfl`. -/
theorem arcTwoBlockRootTransposition_samePartitionFresh_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
