import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCupWindowScanSplit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshComponentInvisibility
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentGodement

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

end FX1Poly.Polygraph
