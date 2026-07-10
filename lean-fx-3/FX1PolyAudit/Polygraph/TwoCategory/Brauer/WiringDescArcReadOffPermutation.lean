import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcReadOffPermutation

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcReadOffPermutation — zero-axiom gate (BRAUER-MIDDLE r15)

Per-declaration zero-axiom gate for the T-CLOSE opening: the finite-pigeonhole range-permutation surjectivity
(`isPermutationOfRange_surjective`), the `permInverse` length / positional read-off (`permInverse_length`,
`natListGetAtPermInversePerm`), the gate-preservation `isPermutationOfRange_permInverse`, the concrete-witness
non-vacuity bundle, and the honesty markers + r15 ledger.  The gate-preservation assertion transitively covers every
re-derived private helper (the `propext`-free `Nat.beq` deciders, the range / map / membership kit, the
first-occurrence erase, the length-bound pigeonhole, and the roundtrip / injectivity bridges).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the finite-pigeonhole surjectivity + the permInverse read-offs
#assert_no_axioms FX1Poly.Polygraph.isPermutationOfRange_surjective
#assert_no_axioms FX1Poly.Polygraph.permInverse_length
#assert_no_axioms FX1Poly.Polygraph.natListGetAtPermInversePerm

-- the headline gate-preservation
#assert_no_axioms FX1Poly.Polygraph.isPermutationOfRange_permInverse

-- the concrete-witness non-vacuity bundle
#assert_no_axioms FX1Poly.Polygraph.isPermutationOfRange_threeCycle_witness
#assert_no_axioms FX1Poly.Polygraph.isPermutationOfRange_surjective_threeCycle
#assert_no_axioms FX1Poly.Polygraph.permInverse_threeCycle_eval
#assert_no_axioms FX1Poly.Polygraph.isPermutationOfRange_permInverse_threeCycle

-- the T-CLOSE truth-probes (read-off orders ARE range-permutations on concrete diagrams)
#assert_no_axioms FX1Poly.Polygraph.freshMixedProbeDiagram
#assert_no_axioms FX1Poly.Polygraph.readOffBottomOrder_isPermutationOfRange_adversarialB
#assert_no_axioms FX1Poly.Polygraph.readOffTopOrder_isPermutationOfRange_adversarialB
#assert_no_axioms FX1Poly.Polygraph.readOffBottomOrder_isPermutationOfRange_freshMixed
#assert_no_axioms FX1Poly.Polygraph.readOffTopOrder_isPermutationOfRange_freshMixed

-- the honesty markers + ledger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasPermInverseRangePreservation
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasReadOffOrderPermutation
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasReadOffOrderPermutationProbe
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r15Ledger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerMiddleR15Complete

end FX1PolyAudit
