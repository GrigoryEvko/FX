import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingPartnerConjugation

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingPartnerConjugation — zero-axiom gate

Per-declaration zero-axiom gate for the r9 PARTNER-field σ-conjugation.  In the perfect-matching regime
(`ArcBoundaryCensus` ≤ 2 boundary ends per component + `ArcPerfectMatching` each index has a distinct
same-component partner, both shipped and fold-preserved), the faithful `2⇒2` crossing conjugates the whole
`diagram.partner` list by the boundary transposition `transposeAdjacent (bottomCount + position)`:
`partner_stepCrossArc_eq_conjugate`.

The build: NODE 1 (`transposeAdjacent_involutive` / `_injective`, the one new transposition fact, joint
structural recursion — `rfl`-clean), NODE 2 (`partnerIndexOf_eq_of_uniqueCandidate`, a census-free min-index pin
built from the shipped scan kit), NODE 3 (`partnerIndexOf_stepCrossArc_eq_conjugate`, the pointwise σ-transfer
via the shipped census-uniqueness pin + the perfect-matching no-fixed-point bridge + the boundary anchor), and
NODE 4 (the whole-list lift by list extensionality).  Non-vacuity: `arcCrossingPartnerConjugation_seed_confirms`
fires the flip at every fresh-seed crossing via the shipped initial census + matching.  The honest wall
(`arcCrossingPartnerConjugation_triComponent_stays_refuted`) records that the UNCONDITIONAL claim is genuinely
false off the regime.

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the two
are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- NODE 1: the transposition involution + injectivity
#assert_no_axioms FX1Poly.Polygraph.transposeAdjacent_involutive
#assert_no_axioms FX1Poly.Polygraph.transposeAdjacent_injective

-- NODE 2: the census-free min-index pin
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_eq_of_uniqueCandidate

-- NODE 3: the pointwise σ-conjugation
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_stepCrossArc_eq_conjugate

-- NODE 4: the whole-list conjugation + non-vacuity witnesses + the honest wall
#assert_no_axioms FX1Poly.Polygraph.partner_stepCrossArc_eq_conjugate
#assert_no_axioms FX1Poly.Polygraph.arcCrossingPartnerConjugation_seed_confirms
#assert_no_axioms FX1Poly.Polygraph.arcCrossingPartnerConjugation_seed2_confirms
#assert_no_axioms FX1Poly.Polygraph.arcCrossingPartnerConjugation_triComponent_stays_refuted

-- honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCrossingPartnerConjugationInMatchingRegime
#assert_no_axioms FX1Poly.Polygraph.arcCrossingPartnerConjugation_unconditionalPartner_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCrossingPartnerConjugation_countField_stays_true
#assert_no_axioms FX1Poly.Polygraph.arcCrossingPartnerConjugation_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCrossingPartnerConjugation_samePartitionFreshProof_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.transposeAdjacent_involutive
#print axioms FX1Poly.Polygraph.transposeAdjacent_injective
#print axioms FX1Poly.Polygraph.partnerIndexOf_eq_of_uniqueCandidate
#print axioms FX1Poly.Polygraph.partnerIndexOf_stepCrossArc_eq_conjugate
#print axioms FX1Poly.Polygraph.partner_stepCrossArc_eq_conjugate
#print axioms FX1Poly.Polygraph.arcCrossingPartnerConjugation_seed_confirms
#print axioms FX1Poly.Polygraph.arcCrossingPartnerConjugation_seed2_confirms
#print axioms FX1Poly.Polygraph.arcCrossingPartnerConjugation_triComponent_stays_refuted
#print axioms FX1Poly.Polygraph.fxMode_hasArcCrossingPartnerConjugationInMatchingRegime
#print axioms FX1Poly.Polygraph.arcCrossingPartnerConjugation_unconditionalPartner_stays_false
#print axioms FX1Poly.Polygraph.arcCrossingPartnerConjugation_countField_stays_true
#print axioms FX1Poly.Polygraph.arcCrossingPartnerConjugation_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcCrossingPartnerConjugation_samePartitionFreshProof_stays_false

end FX1PolyAudit
