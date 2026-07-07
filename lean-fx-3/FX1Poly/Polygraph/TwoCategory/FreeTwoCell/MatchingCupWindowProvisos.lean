import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCupWindowScanSplit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshComponentInvisibility
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentGodement
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyAppendSplit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleySurvivorOrder

/-! # MatchingCupWindowProvisos — discharging the single-cup partner-scan window provisos

`MatchingCupWindowScanSplit.findPartnerScan_range_cupWindowSplit` threads the four generic interleave pieces into
one scan equation MODULO two semantic hypotheses discharged at the FOLDED cup state:

  * `windowPairFails` — the two fresh cup legs `nextFresh`, `nextFresh + 1` FAIL the survivor's exclude-and-root
    test (they are NOT in the survivor's component);
  * `testCorr` — the composite/fresh root correspondence on the survivor/top ports under the index shift.

And `findPartnerScan_range_frontSegmentMisses` takes `frontFails` — the survivor bottom port shares no component
with any OTHER bottom port.

This file discharges the BOUNDED union-find core of the first (`windowPairFails`) and reframes the third
(`frontFails`) against the shipped bottom-preservation frame.  These are NOT the keystone-coupling wall (the
covariant `List Nat` monotone map refutation); they are bounded rigidity facts about fresh cup legs and the
fixed bottom prefix.

  * ★ `stepCup_freshLeg_offSurvivor` — after a single cup, a fresh leg `nextFresh` or `nextFresh + 1` shares no
    component with any below-fresh survivor node.  Pure union-find: both fresh legs are parentless, so the join
    roots them at `nextFresh + 1`, ABOVE the survivor's below-`nextFresh` root.
  * ★ `stepCup_windowPairFails_atFreshLegs` — the exact `windowPairFails` boolean shape at the two fresh legs:
    the exclude-and-root conjunct is `false` because its right conjunct (the root test) is `false`.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Proviso (1) — the fresh cup legs miss the survivor's component -/

/-- ★ **A fresh cup leg shares no component with a below-fresh survivor.**  A cup joins its two FRESH legs
`nextFresh` and `nextFresh + 1` (`stepCup_links`); both are parentless in the pre-cup forest (every existing
edge's child sits below `nextFresh`), so their pre-join roots are themselves, and the join reroots BOTH to
`nextFresh + 1`.  A survivor node `< nextFresh` keeps its below-`nextFresh` root through the join (its root chain
never reaches a fresh id).  The fresh leg's post-join root `nextFresh + 1` is therefore strictly above the
survivor's root, so the two are in different components.  This is the bounded core of `windowPairFails`. -/
theorem stepCup_freshLeg_offSurvivor (state : WireState) (position : Nat)
    (fresh : WireStateFresh state) (forest : isUnionFindForest state.links)
    (leg survivorNode : Nat)
    (legRange : leg = state.nextFresh ∨ leg = state.nextFresh + 1)
    (survivorBelow : survivorNode < state.nextFresh) :
    isSameComponent (stepCup state position).links leg survivorNode = false := by
  have childBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2 edge edgeInLinks).1
  have parentBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2 edge edgeInLinks).2
  have rootNf : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_parentless _ _
      (unionFindParent_none_of_lt state.nextFresh state.links childBelow state.nextFresh (Nat.le_refl _))
  have rootNfSucc : unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_of_parentless _ _
      (unionFindParent_none_of_lt state.nextFresh state.links childBelow (state.nextFresh + 1)
        (Nat.le_succ _))
  have rootSurv : unionFindRootOf state.links survivorNode < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh parentBelow survivorNode survivorBelow
  -- The survivor's post-join root is unchanged (guard false: nf ≠ survivorRoot).
  have survGuard : (unionFindRootOf state.links state.nextFresh
      == unionFindRootOf state.links survivorNode) = false := by
    apply decide_eq_false
    intro rootsEqual
    rw [rootNf] at rootsEqual
    exact absurd (rootsEqual ▸ rootSurv) (Nat.lt_irrefl state.nextFresh)
  have survRootJoin : unionFindRootOf (stepCup state position).links survivorNode
      = unionFindRootOf state.links survivorNode := by
    rw [stepCup_links, unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
      survivorNode forest, survGuard, if_neg (fun trueEqTrue => Bool.noConfusion trueEqTrue)]
  -- The fresh leg's post-join root is nextFresh + 1 in both cases.
  have legRootJoin : unionFindRootOf (stepCup state position).links leg = state.nextFresh + 1 := by
    rw [stepCup_links, unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
      leg forest]
    rcases legRange with legIsNf | legIsNfSucc
    · rw [legIsNf, rootNf]
      have selfGuard : (state.nextFresh == state.nextFresh) = true := by
        apply decide_eq_true; rfl
      rw [selfGuard, if_pos rfl, rootNfSucc]
    · rw [legIsNfSucc, rootNfSucc]
      have crossGuard : (unionFindRootOf state.links state.nextFresh == state.nextFresh + 1) = false := by
        rw [rootNf]
        apply decide_eq_false
        intro nfEqSucc
        exact absurd nfEqSucc (Nat.ne_of_lt (Nat.lt_succ_self state.nextFresh))
      rw [crossGuard, if_neg (fun trueEqTrue => Bool.noConfusion trueEqTrue)]
  -- The two post-join roots differ: nf + 1 ≥ nf > survivorRoot.
  show (unionFindRootOf (stepCup state position).links leg
    == unionFindRootOf (stepCup state position).links survivorNode) = false
  rw [legRootJoin, survRootJoin]
  apply decide_eq_false
  intro succEqSurv
  have contradictoryLt : state.nextFresh + 1 < state.nextFresh := succEqSurv ▸ rootSurv
  exact absurd contradictoryLt (Nat.not_lt.mpr (Nat.le_succ state.nextFresh))

/-- ★ **The exact `windowPairFails` boolean at the two fresh legs.**  When the survivor's root in the composite
(post-cup) links is `unionFindRootOf (stepCup state position).links survivorNode` and the boundary read at the
window pair returns the two fresh legs (`legReads`), each window candidate's exclude-and-root conjunct is `false`:
its RIGHT conjunct (the root test) is `false` by `stepCup_freshLeg_offSurvivor`, so the whole `&&` collapses via
`Bool.and_false`.  This is exactly the `windowPairFails` hypothesis of `findPartnerScan_range_cupWindowSplit` at
the single-cup instantiation. -/
theorem stepCup_windowPairFails_atFreshLegs (state : WireState) (position : Nat)
    (fresh : WireStateFresh state) (forest : isUnionFindForest state.links)
    (boundaryNodes : List Nat) (windowPosition survivorNode excludeShifted : Nat)
    (survivorBelow : survivorNode < state.nextFresh)
    (legReads : ∀ leg, leg ∈ [windowPosition, windowPosition + 1] →
      (natListGetAt boundaryNodes leg = state.nextFresh ∨ natListGetAt boundaryNodes leg = state.nextFresh + 1)) :
    ∀ leg, leg ∈ [windowPosition, windowPosition + 1] →
      (leg != excludeShifted
          && unionFindRootOf (stepCup state position).links (natListGetAt boundaryNodes leg)
              == unionFindRootOf (stepCup state position).links survivorNode) = false := by
  intro leg legInWindow
  have rootTestFalse :
      (unionFindRootOf (stepCup state position).links (natListGetAt boundaryNodes leg)
        == unionFindRootOf (stepCup state position).links survivorNode) = false := by
    have offSurvivor := stepCup_freshLeg_offSurvivor state position fresh forest
      (natListGetAt boundaryNodes leg) survivorNode (legReads leg legInWindow) survivorBelow
    exact offSurvivor
  rw [rootTestFalse, Bool.and_false]

/-! ## Proviso (2) — the survivor's partner is not a bottom port (the front-segment miss frame)

`findPartnerScan_range_frontSegmentMisses` takes `frontFails`: no bottom candidate (other than the survivor
itself) shares the survivor's component in the COMPOSITE (whole-valley) links.  A cup block, run after the cap
block, only splices FRESH top arcs and NEVER touches the fixed bottom prefix `0 … bottomCount-1`
(`processSpine_isSameComponent_bottom_ofAllCupArity`), so the composite bottom-bottom same-component relation
equals the cap-block mid-state's.  This frame turns "survivor isolated among bottoms at the mid-state" (the
through-strand content the cap block supplies — the standing valley-descent residual #2185) into the exact
`frontFails` boolean at the composite state, ready to feed `findPartnerScan_range_frontSegmentMisses`. -/

/-- ★ **The `frontFails` frame at a cup-block composite state.**  Given the survivor bottom port is isolated
among the bottom ports at the cap-block mid-state (`midIsolated` — no other bottom shares its component), a pure
cup block preserves that (`processSpine_isSameComponent_bottom_ofAllCupArity`), so at the composite
(post-cup-block) state every bottom candidate's exclude-and-root conjunct is `false`: the diagonal by the `!=`
conjunct, every off-diagonal bottom by the preserved isolation (the root conjunct).  This is precisely the
`frontFails` hypothesis of `findPartnerScan_range_frontSegmentMisses`. -/
theorem cupBlock_frontFails_ofMidIsolated
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (cupPure : AllCupArity cupBlock) (midState : WireState)
    (conditions : MatchingSwapStateConditions bottomCount midState)
    (survivorIndex : Nat) (survivorBelow : survivorIndex < bottomCount)
    (midIsolated : ∀ candidate, candidate < bottomCount → candidate ≠ survivorIndex →
      isSameComponent midState.links candidate survivorIndex = false) :
    ∀ candidate, candidate ∈ List.range bottomCount →
      (candidate != survivorIndex
          && unionFindRootOf (processSpine midState cupBlock).links
              (natListGetAt (matchingBoundaryNodes bottomCount (processSpine midState cupBlock)) candidate)
            == unionFindRootOf (processSpine midState cupBlock).links
              (natListGetAt (matchingBoundaryNodes bottomCount (processSpine midState cupBlock)) survivorIndex))
        = false := by
  intro candidate candidateInRange
  have candidateBelow : candidate < bottomCount := mem_range_imp_lt candidateInRange
  rw [matchingBoundaryNodes_getAt_bottom bottomCount (processSpine midState cupBlock) candidate candidateBelow,
    matchingBoundaryNodes_getAt_bottom bottomCount (processSpine midState cupBlock) survivorIndex survivorBelow]
  match Nat.decEq candidate survivorIndex with
  | isTrue candidateEqSurvivor =>
      rw [candidateEqSurvivor]
      have selfBeq : (survivorIndex == survivorIndex) = true := by apply decide_eq_true; rfl
      have diagFalse : (survivorIndex != survivorIndex) = false := congrArg Bool.not selfBeq
      rw [diagFalse]; rfl
  | isFalse candidateNeSurvivor =>
      have rootTestFalse :
          (unionFindRootOf (processSpine midState cupBlock).links candidate
            == unionFindRootOf (processSpine midState cupBlock).links survivorIndex) = false := by
        show isSameComponent (processSpine midState cupBlock).links candidate survivorIndex = false
        rw [processSpine_isSameComponent_bottom_ofAllCupArity bottomCount cupBlock cupPure midState
          conditions candidate survivorIndex candidateBelow survivorBelow]
        exact midIsolated candidate candidateBelow candidateNeSurvivor
      rw [rootTestFalse, Bool.and_false]

/-! ## Proviso (3) — the composite/fresh root correspondence (`testCorr`)

`findPartnerScan_range_cupWindowSplit` takes `testCorr`: at every fresh (mid-state) candidate, the composite
exclude-and-root test at the SHIFTED boundary index equals the fresh exclude-and-root test.  This is the crux the
recon flagged as a two-run view-simulation.  Its BOUNDED CORE is the fact that a cup is component-transparent to
OLD nodes — it joins only its two fresh legs, so the root of every below-`nextFresh` node is untouched
(`stepCup_unionFindRootOf_oldNode`).  Given that, plus the boundary-read shift correspondence
(`natListGetAt_shiftPastPosition`, shipped in `ValleySurvivorOrder`) and the injectivity of the two-zone splice
map, the per-candidate correspondence assembles WITHOUT any renaming — `testCorr_ofCorrespondences` packages the
reduction so the abstract `testCorr` follows from three concrete-instance readouts (all bounded). -/

/-- ★ **A cup preserves the root of every OLD node.**  A cup joins only its two fresh legs `nextFresh`,
`nextFresh + 1` (`stepCup_links`); both are parentless in the pre-cup forest, so the join's redirect guard
`rootOf nextFresh == rootOf oldNode` is `false` for any below-`nextFresh` node (whose root also sits below
`nextFresh`).  Hence the old node's post-cup root is exactly its pre-cup root — the component-transparency that
makes the single-cup `testCorr` a bounded fact rather than a renaming simulation. -/
theorem stepCup_unionFindRootOf_oldNode (state : WireState) (position : Nat)
    (fresh : WireStateFresh state) (forest : isUnionFindForest state.links)
    (node : Nat) (nodeBelow : node < state.nextFresh) :
    unionFindRootOf (stepCup state position).links node = unionFindRootOf state.links node := by
  have childBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2 edge edgeInLinks).1
  have parentBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2 edge edgeInLinks).2
  have rootNf : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_parentless _ _
      (unionFindParent_none_of_lt state.nextFresh state.links childBelow state.nextFresh (Nat.le_refl _))
  have rootNode : unionFindRootOf state.links node < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh parentBelow node nodeBelow
  rw [stepCup_links, unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
    node forest]
  have guardFalse : (unionFindRootOf state.links state.nextFresh == unionFindRootOf state.links node) = false := by
    rw [rootNf]
    apply decide_eq_false
    intro nfEqRoot
    exact Nat.lt_irrefl (unionFindRootOf state.links node) (nfEqRoot ▸ rootNode)
  rw [guardFalse, if_neg (fun trueEqTrue => Bool.noConfusion trueEqTrue)]

/-- ★ **`testCorr` from three concrete-instance correspondences (no renaming).**  The abstract composite/fresh
exclude-and-root correspondence follows from: (i) the SHIFT reads the SAME node at every fresh candidate
(`readsAgree` — the boundary-read shift, `natListGetAt_shiftPastPosition`); (ii) the composite links root that
shared node exactly as the fresh links do (`rootsAgree` — cup component-transparency,
`stepCup_unionFindRootOf_oldNode`); and (iii) the survivor's composite root equals its fresh root
(`survivorRootAgree`), together with the two-zone map's injectivity (`shiftInjective`).  The right conjuncts of
the two `&&`s coincide by (i)+(ii)+(iii); the `!=` conjuncts coincide by injectivity.  This discharges the
`testCorr` hypothesis of `findPartnerScan_range_cupWindowSplit` at the single-cup instantiation with NO
order-dependent renaming — the two-run correspondence is a bounded readout, not a simulation. -/
theorem testCorr_ofCorrespondences
    (compositeLinks freshLinks : List (Nat × Nat))
    (compositeBoundary freshBoundary : List Nat)
    (compositeRoot freshRoot freshExclude : Nat) (indexShift : Nat → Nat)
    (candidateRange : List Nat)
    (shiftInjective : ∀ firstIndex secondIndex, indexShift firstIndex = indexShift secondIndex →
      firstIndex = secondIndex)
    (survivorRootAgree : compositeRoot = freshRoot)
    (readsAgree : ∀ candidate, candidate ∈ candidateRange →
      natListGetAt compositeBoundary (indexShift candidate) = natListGetAt freshBoundary candidate)
    (rootsAgree : ∀ candidate, candidate ∈ candidateRange →
      unionFindRootOf compositeLinks (natListGetAt freshBoundary candidate)
        = unionFindRootOf freshLinks (natListGetAt freshBoundary candidate)) :
    ∀ candidate, candidate ∈ candidateRange →
      (indexShift candidate != indexShift freshExclude
          && unionFindRootOf compositeLinks
              (natListGetAt compositeBoundary (indexShift candidate)) == compositeRoot)
        = (candidate != freshExclude
            && unionFindRootOf freshLinks (natListGetAt freshBoundary candidate) == freshRoot) := by
  intro candidate candidateInRange
  -- The right conjuncts coincide: same node, same root, same target.
  have rightConjunctAgree :
      (unionFindRootOf compositeLinks (natListGetAt compositeBoundary (indexShift candidate)) == compositeRoot)
        = (unionFindRootOf freshLinks (natListGetAt freshBoundary candidate) == freshRoot) := by
    rw [readsAgree candidate candidateInRange, rootsAgree candidate candidateInRange, survivorRootAgree]
  -- The exclude conjuncts coincide by injectivity of the shift.
  have excludeConjunctAgree :
      (indexShift candidate != indexShift freshExclude) = (candidate != freshExclude) := by
    have beqAgree : (indexShift candidate == indexShift freshExclude) = (candidate == freshExclude) := by
      cases candidateEqExclude : candidate == freshExclude with
      | true =>
          have candidateIsExclude : candidate = freshExclude := of_decide_eq_true candidateEqExclude
          rw [candidateIsExclude]
          apply decide_eq_true; rfl
      | false =>
          apply decide_eq_false
          intro shiftEqual
          have candidateIsExclude : candidate = freshExclude :=
            shiftInjective candidate freshExclude shiftEqual
          rw [candidateIsExclude] at candidateEqExclude
          have selfBeq : (freshExclude == freshExclude) = true := by apply decide_eq_true; rfl
          rw [selfBeq] at candidateEqExclude
          exact Bool.noConfusion candidateEqExclude
    show (!(indexShift candidate == indexShift freshExclude)) = (!(candidate == freshExclude))
    rw [beqAgree]
  rw [excludeConjunctAgree, rightConjunctAgree]

end FX1Poly.Polygraph
