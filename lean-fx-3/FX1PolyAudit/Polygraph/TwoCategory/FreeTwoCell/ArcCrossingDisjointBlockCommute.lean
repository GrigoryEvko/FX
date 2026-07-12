import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingDisjointBlockCommute

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingDisjointBlockCommute — zero-axiom gate

Per-declaration zero-axiom gate for the r10 DISJOINT-BLOCK GODEMENT INDEPENDENCE of the faithful `2⇒2` crossing:
two crossings at horizontally-disjoint positions (`leftPivot + 2 ≤ rightPivot`) commute on the WHOLE extract,
UNCONDITIONALLY (no perfect-matching regime).

The build: NODE 1 (`transposeAdjacent_disjointCommute`, the one new algebraic fact — two adjacent transpositions
at disjoint pivots commute pointwise on the naturals, a five-zone case split off the shipped r8 equational
lemmas, pivots separated by `Nat.decEq`), NODE 2 (`natListSwapTwoAt_disjointCommute`, the wire-list lift by the
shipped anchor `natListGetAt_natListSwapTwoAt` + list extensionality), NODE 3 (the state/extract corollary chain
via `congrArg`, plus the general `consCongr` faithful-step invariants).  The whole-extract commute delivers the
COUNT field AND the PARTNER field at once, with no regime — strictly stronger than the recon's split (which
anticipated count-unconditional / partner-regime-gated), because two orderings yield literally the same state.
Non-vacuity: `arcCrossingDisjointBlockCommute_seed_confirms` fires at every fresh-seed crossing pair;
`arcCrossingDisjointBlockCommute_offRegime_confirms` fires on the r8 hostile three-port component (off the
matching regime, where the single-crossing partner conjugation is refuted).

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the two
are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- NODE 1: the disjoint pointwise transposition commute (the one new algebraic fact)
#assert_no_axioms FX1Poly.Polygraph.transposeAdjacent_disjointCommute

-- NODE 2: the wire-list disjoint swap commute
#assert_no_axioms FX1Poly.Polygraph.natListSwapTwoAt_disjointCommute

-- NODE 3a: the general consCongr faithful-step invariants
#assert_no_axioms FX1Poly.Polygraph.stepCrossArc_openWires_length
#assert_no_axioms FX1Poly.Polygraph.stepCrossArc_links
#assert_no_axioms FX1Poly.Polygraph.stepCrossArc_nextFresh
#assert_no_axioms FX1Poly.Polygraph.stepCrossArc_loops
#assert_no_axioms FX1Poly.Polygraph.stepCrossArc_cupEventNodes
#assert_no_axioms FX1Poly.Polygraph.stepCrossArc_capEventNodes

-- NODE 3b: the state/extract disjoint commute + the field-level corollaries
#assert_no_axioms FX1Poly.Polygraph.stepCrossArc_disjointCommute
#assert_no_axioms FX1Poly.Polygraph.extractArc_stepCrossArc_disjointCommute
#assert_no_axioms FX1Poly.Polygraph.internalCupCounts_stepCrossArc_disjointCommute
#assert_no_axioms FX1Poly.Polygraph.internalCapCounts_stepCrossArc_disjointCommute
#assert_no_axioms FX1Poly.Polygraph.partner_stepCrossArc_disjointCommute

-- non-vacuity witnesses (fresh seed + off the matching regime)
#assert_no_axioms FX1Poly.Polygraph.arcCrossingDisjointBlockCommute_seed_confirms
#assert_no_axioms FX1Poly.Polygraph.arcCrossingDisjointBlockCommute_offRegime_confirms

-- honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCrossingDisjointBlockCommute
#assert_no_axioms FX1Poly.Polygraph.arcCrossingDisjointBlockCommute_countField_stays_true
#assert_no_axioms FX1Poly.Polygraph.arcCrossingDisjointBlockCommute_partnerRegime_stays_true
#assert_no_axioms FX1Poly.Polygraph.arcCrossingDisjointBlockCommute_unconditionalSinglePartner_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCrossingDisjointBlockCommute_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCrossingDisjointBlockCommute_samePartitionFreshProof_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.transposeAdjacent_disjointCommute
#print axioms FX1Poly.Polygraph.natListSwapTwoAt_disjointCommute
#print axioms FX1Poly.Polygraph.stepCrossArc_openWires_length
#print axioms FX1Poly.Polygraph.stepCrossArc_disjointCommute
#print axioms FX1Poly.Polygraph.extractArc_stepCrossArc_disjointCommute
#print axioms FX1Poly.Polygraph.internalCupCounts_stepCrossArc_disjointCommute
#print axioms FX1Poly.Polygraph.internalCapCounts_stepCrossArc_disjointCommute
#print axioms FX1Poly.Polygraph.partner_stepCrossArc_disjointCommute
#print axioms FX1Poly.Polygraph.arcCrossingDisjointBlockCommute_seed_confirms
#print axioms FX1Poly.Polygraph.arcCrossingDisjointBlockCommute_offRegime_confirms
#print axioms FX1Poly.Polygraph.fxMode_hasArcCrossingDisjointBlockCommute
#print axioms FX1Poly.Polygraph.arcCrossingDisjointBlockCommute_countField_stays_true
#print axioms FX1Poly.Polygraph.arcCrossingDisjointBlockCommute_partnerRegime_stays_true
#print axioms FX1Poly.Polygraph.arcCrossingDisjointBlockCommute_unconditionalSinglePartner_stays_false
#print axioms FX1Poly.Polygraph.arcCrossingDisjointBlockCommute_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcCrossingDisjointBlockCommute_samePartitionFreshProof_stays_false

end FX1PolyAudit
