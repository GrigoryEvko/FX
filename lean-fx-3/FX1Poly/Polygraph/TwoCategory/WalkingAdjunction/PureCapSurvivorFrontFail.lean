import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.PureCapSurvivorUnlinked
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCupWindowScanSplit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPairSeparation

/-! # PureCapSurvivorFrontFail — the survivor front-fail + top-segment drop (Piece II tail, 2b step 1)

Brick (2a) proved every SURVIVING open wire of a pure-cap block is `ArcNodeUnlinked` — a singleton
component.  This file turns that into the FIRST half of the survivor read-off (2b): a survivor
bottom port's partner scan drops entirely to the TOP segment.

Because a survivor bottom port `survivor` (`< bottomCount`, unlinked) is its own root and no other
node roots to it (`nodeSetHoldsAtRoot` at the closed node-set `(· ≠ survivor)`), EVERY bottom
candidate `0 … bottomCount-1` FAILS the survivor's exclude-and-root test — the survivor is excluded
by the bang-inequality, and every OTHER bottom port's root avoids `survivor`.  So the partner scan
over the whole boundary range drops to the top segment
(`findPartnerScan_range_frontSegmentMisses`): the survivor's partner is a TOP port.

  * `unionFindRootOf_ne_ofUnlinked` — no node other than an unlinked node roots to it.
  * `partnerScanFrontTest_false_ofUnlinked` — every bottom candidate fails the survivor's test.
  * ★ `partnerIndexOf_survivor_dropsToTop` — the survivor's `partnerIndexOf` equals its partner scan
    restricted to the top segment.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **No node other than an unlinked node roots to it.**  With the node-set `(· ≠ excludeNode)`
closed under the links (every edge misses `excludeNode`, which is exactly `ArcNodeUnlinked`), the
root of any node distinct from `excludeNode` stays distinct from it (`nodeSetHoldsAtRoot`). -/
theorem unionFindRootOf_ne_ofUnlinked (links : List (Nat × Nat)) {excludeNode : Nat}
    (excludeUnlinked : ArcNodeUnlinked links excludeNode) (node : Nat) (nodeNe : node ≠ excludeNode) :
    unionFindRootOf links node ≠ excludeNode :=
  nodeSetHoldsAtRoot (fun candidate => candidate ≠ excludeNode) links
    (fun edge edgeMem => excludeUnlinked edge edgeMem) node nodeNe

/-- **Every bottom candidate fails an unlinked survivor's exclude-and-root test.**  The survivor
sits at boundary read `survivor` (the range prefix, `matchingBoundaryNodes_getAt_bottom`) and is its
own root; a candidate bottom port either IS the survivor (excluded by the bang-inequality) or has a
root avoiding the survivor (`unionFindRootOf_ne_ofUnlinked`), so the whole test is `false`. -/
theorem partnerScanFrontTest_false_ofUnlinked (links : List (Nat × Nat)) (bottomCount : Nat)
    (state : WireState) {excludeNode : Nat} (excludeUnlinked : ArcNodeUnlinked links excludeNode)
    (candidate : Nat) (candidateBelow : candidate < bottomCount) :
    (candidate != excludeNode
        && unionFindRootOf links (natListGetAt (matchingBoundaryNodes bottomCount state) candidate)
            == excludeNode) = false := by
  rw [matchingBoundaryNodes_getAt_bottom bottomCount state candidate candidateBelow]
  cases candidateIsExclude : (candidate == excludeNode) with
  | true =>
      have candidateBne : (candidate != excludeNode) = false := by
        show (!(candidate == excludeNode)) = false
        rw [candidateIsExclude]; rfl
      rw [candidateBne]; exact Bool.false_and _
  | false =>
      have candidateNe : candidate ≠ excludeNode := of_decide_eq_false candidateIsExclude
      have rootBeqFalse : (unionFindRootOf links candidate == excludeNode) = false := by
        cases rootIsExclude : (unionFindRootOf links candidate == excludeNode) with
        | true =>
            exact absurd (of_decide_eq_true rootIsExclude)
              (unionFindRootOf_ne_ofUnlinked links excludeUnlinked candidate candidateNe)
        | false => rfl
      rw [rootBeqFalse]; exact Bool.and_false _

/-- ★ **A survivor bottom port's partner scan drops to the top segment.**  The survivor is its own
root (`unionFindRootOf_eq_self_ofUnlinked`) at boundary read `survivor`, and every bottom candidate
fails its test (`partnerScanFrontTest_false_ofUnlinked`), so the whole-range partner scan drops to
the top-index segment `(List.range topCount).map (bottomCount + ·)`
(`findPartnerScan_range_frontSegmentMisses`).  The survivor's partner is therefore a TOP port — the
cap-side restriction re-ranks survivors only within the top segment. -/
theorem partnerIndexOf_survivor_dropsToTop (links : List (Nat × Nat)) (bottomCount : Nat)
    (state : WireState) {survivor : Nat} (survivorBelow : survivor < bottomCount)
    (survivorUnlinked : ArcNodeUnlinked links survivor) (topCount : Nat) :
    partnerIndexOf links (matchingBoundaryNodes bottomCount state) (bottomCount + topCount) survivor
      = findPartnerScan links (matchingBoundaryNodes bottomCount state) survivor survivor
          ((List.range topCount).map (fun offset => bottomCount + offset)) := by
  unfold partnerIndexOf
  rw [matchingBoundaryNodes_getAt_bottom bottomCount state survivor survivorBelow,
    unionFindRootOf_eq_self_ofUnlinked links survivorUnlinked]
  exact findPartnerScan_range_frontSegmentMisses links (matchingBoundaryNodes bottomCount state)
    survivor survivor bottomCount topCount
    (fun candidate candidateMem =>
      partnerScanFrontTest_false_ofUnlinked links bottomCount state survivorUnlinked candidate
        (mem_range_imp_lt candidateMem))

/-! ## Honesty marker -/

/-- **Honesty marker — the survivor front-fail + top-segment drop (2b step 1) is SHIPPED.**  Using
brick (2a) (survivors are unlinked), every bottom candidate fails a survivor's partner test, so the
survivor's `partnerIndexOf` equals its partner scan restricted to the TOP segment.  NOT yet shipped:
the top-segment FIRST-HIT read-off — that the survivor's partner top port sits at
`bottomCount + (its rank among the survivors in the final open wires)`, i.e. the scan over
`(List.range topCount).map (bottomCount + ·)` first passes at the survivor's open-wire position
(distinct survivors give a unique hit).  That top-segment first-hit-at-rank lemma is the remaining
half of (2b); it feeds the F/G assembly of the valley-append split.  No gate flag is flipped.
`= true`. -/
def fxMode_hasPureCapSurvivorFrontFail : Bool := true

end FX1Poly.Polygraph
