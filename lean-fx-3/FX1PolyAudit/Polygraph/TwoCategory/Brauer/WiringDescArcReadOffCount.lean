import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcReadOffCount

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcReadOffCount — zero-axiom gate (BRAUER-MIDDLE r16)

Per-declaration zero-axiom gate for the counting round: the arc-class guards, the three-way partition count
(`partitionCountThree` + `partitionThree_of_involution`), and the crux truth-probes.  The two partition assertions
transitively cover every re-derived private helper (the `propext`-free `Nat.blt` / `Nat.ble` deciders, the `Bool`
conjunction closers, the range-membership kit, and the six-summand rearrangement).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the arc-class guards + the counting engine
#assert_no_axioms FX1Poly.Polygraph.capSmallerGuard
#assert_no_axioms FX1Poly.Polygraph.capLargerGuard
#assert_no_axioms FX1Poly.Polygraph.throughBottomGuard
#assert_no_axioms FX1Poly.Polygraph.countTrue
#assert_no_axioms FX1Poly.Polygraph.onlyOneTrueThree

-- the three-way partition count + the involution-gated per-index classification
#assert_no_axioms FX1Poly.Polygraph.partitionCountThree
#assert_no_axioms FX1Poly.Polygraph.partitionThree_of_involution

-- the crux truth-probes on the recon hand-worked partners
#assert_no_axioms FX1Poly.Polygraph.cruxCount_probe_adversarialB
#assert_no_axioms FX1Poly.Polygraph.cruxCount_probe_freshMixed
#assert_no_axioms FX1Poly.Polygraph.cruxCount_probe_allCaps
#assert_no_axioms FX1Poly.Polygraph.cruxCount_probe_allThrough
#assert_no_axioms FX1Poly.Polygraph.cruxCount_probe_widthOne
#assert_no_axioms FX1Poly.Polygraph.cruxCount_probe_empty

-- the filterMap length ↔ countTrue bridge + the three read-off length counts
#assert_no_axioms FX1Poly.Polygraph.filterMapLength_eq_countTrue
#assert_no_axioms FX1Poly.Polygraph.capArcFeetIndices_length_eq_count
#assert_no_axioms FX1Poly.Polygraph.throughStrandBottoms_length_eq_count
#assert_no_axioms FX1Poly.Polygraph.capLargerFeetIndices
#assert_no_axioms FX1Poly.Polygraph.capLargerFeetIndices_length_eq_count

-- filterMap completeness (K3), the erase-kit length equality (K4), and the pairing bijection (crux-of-crux)
#assert_no_axioms FX1Poly.Polygraph.memFilterMapGuardComplete
#assert_no_axioms FX1Poly.Polygraph.distinctSameMembersLengthEq
#assert_no_axioms FX1Poly.Polygraph.capLargerFeetIndices_length_eq

-- the doubling, the crux, and the bottom read-off width-length identity + boundedness
#assert_no_axioms FX1Poly.Polygraph.expandBottomFeetPairs_length
#assert_no_axioms FX1Poly.Polygraph.capArcFeetTwiceThroughSumsToBottom
#assert_no_axioms FX1Poly.Polygraph.bottomReadOffOrderLength
#assert_no_axioms FX1Poly.Polygraph.memberBoundedBottomReadOff
#assert_no_axioms FX1Poly.Polygraph.bottomReadOffOrderBounded

-- the bottom read-off distinctness + the general bottom-side IsPermutationOfRange (T-CLOSE bottom side)
#assert_no_axioms FX1Poly.Polygraph.capArcFeet_distinct
#assert_no_axioms FX1Poly.Polygraph.throughStrandBottoms_distinct
#assert_no_axioms FX1Poly.Polygraph.bottomReadOffOrder_distinct
#assert_no_axioms FX1Poly.Polygraph.readOffBottomOrder_isPermutationOfRange

-- the general bottom E2 roundtrip + the honesty markers + the r16 ledger
#assert_no_axioms FX1Poly.Polygraph.readOffBottomOrder_realizesRoundtrip
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasReadOffBottomOrderPermutation
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasReadOffBottomOrderRoundtrip
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasReadOffTopOrderPermutation
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r16Ledger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerMiddleR16Complete

-- ★ BRAUER r17 (T-CLOSE top side): the TOP arc-class guards + the ∗-dual classification, counting engine, pairing
-- bijection, and the ∗-dual crux.  The two ∗-dual assertions transitively cover the offset-port cancel helpers.
#assert_no_axioms FX1Poly.Polygraph.cupSmallerGuard
#assert_no_axioms FX1Poly.Polygraph.cupLargerGuard
#assert_no_axioms FX1Poly.Polygraph.throughTopGuard
#assert_no_axioms FX1Poly.Polygraph.partnerTopShift
#assert_no_axioms FX1Poly.Polygraph.partitionThree_of_involution_top
#assert_no_axioms FX1Poly.Polygraph.cupCruxCount_probe_adversarialB
#assert_no_axioms FX1Poly.Polygraph.cupCruxCount_probe_freshMixed
#assert_no_axioms FX1Poly.Polygraph.cupCruxCount_probe_nestedCaps
#assert_no_axioms FX1Poly.Polygraph.cupCruxCount_probe_threeCups
#assert_no_axioms FX1Poly.Polygraph.cupArcTopIndices_length_eq_count
#assert_no_axioms FX1Poly.Polygraph.throughStrandTops_length_eq_count
#assert_no_axioms FX1Poly.Polygraph.cupLargerTopIndices
#assert_no_axioms FX1Poly.Polygraph.cupLargerTopIndices_length_eq_count
#assert_no_axioms FX1Poly.Polygraph.cupLargerTopIndices_length_eq
#assert_no_axioms FX1Poly.Polygraph.expandCupTopPairs_length
#assert_no_axioms FX1Poly.Polygraph.cupArcTwiceThroughSumsToTop

-- ★ BRAUER r17 (T-CLOSE top side): the TOP read-off width-length / boundedness / distinctness, the general top
-- IsPermutationOfRange, the permInverse lift, and the universal top E2 roundtrip.
#assert_no_axioms FX1Poly.Polygraph.topReadOffOrderLength
#assert_no_axioms FX1Poly.Polygraph.memberBoundedTopReadOff
#assert_no_axioms FX1Poly.Polygraph.topReadOffOrderBounded
#assert_no_axioms FX1Poly.Polygraph.cupArcTops_distinct
#assert_no_axioms FX1Poly.Polygraph.throughStrandTops_distinct
#assert_no_axioms FX1Poly.Polygraph.topReadOffOrder_distinct
#assert_no_axioms FX1Poly.Polygraph.readOffTopOrder_isPermutationOfRange
#assert_no_axioms FX1Poly.Polygraph.readOffTopOrderInverse_isPermutationOfRange
#assert_no_axioms FX1Poly.Polygraph.readOffTopOrder_realizesRoundtrip

-- ★ BRAUER r17 markers + ledger (the TOP flip + the JOINT read-off-order-permutation flip)
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasReadOffTopOrderRoundtrip
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r17Ledger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerMiddleR17Complete

end FX1PolyAudit
