import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderCrossingRerun

/-! # FX1PolyAudit.Polygraph.TwoCategory.Frobenius.SpiderCrossingRerun — zero-axiom gate (WP-FROB r10, FROB-10)

Per-declaration zero-axiom gate for the row-suffix brick WALL + the comb rerun ASSEMBLY WIRE: the isolated
`RowSuffixCongruence` antecedent + its `SpiderConv` escape + shape witness (P1), the imported crossing canonical
section + the staircase brick + the rerun assembly + non-vacuity (P2), the hook cascade + the two verdict flags (P3),
and the completion ledger (P4).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- FROB-10 P1: the row-level suffix congruence brick (the isolated WALLED antecedent)
#assert_no_axioms FX1Poly.Polygraph.RowSuffixCongruence
#assert_no_axioms FX1Poly.Polygraph.rowSuffixCongruence_escapesToSpiderConv
#assert_no_axioms FX1Poly.Polygraph.rowSuffixCongruence_shape_atEmptySuffix

-- FROB-10 P2: the imported crossing canonical section + the concrete canonicity/straightening witnesses
#assert_no_axioms FX1Poly.Polygraph.frobCrossingStaircase
#assert_no_axioms FX1Poly.Polygraph.frobCrossingStaircase_respectsPermutation
#assert_no_axioms FX1Poly.Polygraph.frobCrossingStaircase_r9jam
#assert_no_axioms FX1Poly.Polygraph.frobCrossingStraightening_r9jam

-- FROB-10 P2: the whole-staircase convertibility brick + the comb rerun assembly + non-vacuity
#assert_no_axioms FX1Poly.Polygraph.RowStaircaseConv
#assert_no_axioms FX1Poly.Polygraph.crossingWords_equalPerm_convRows_ofStaircase
#assert_no_axioms FX1Poly.Polygraph.rowStaircaseConv_atGeneratorCountZero
#assert_no_axioms FX1Poly.Polygraph.crossingWords_equalPerm_convRows_atGeneratorCountZero
#assert_no_axioms FX1Poly.Polygraph.crossingWords_convRows_distantCommute

-- FROB-10 P3: the hook cascade + the partition-permutation bridge non-vacuity + end-to-end firing
#assert_no_axioms FX1Poly.Polygraph.crossingFragment_complete_ofBridgeAndStaircase
#assert_no_axioms FX1Poly.Polygraph.crossingFragmentBridge_atGeneratorCountZero
#assert_no_axioms FX1Poly.Polygraph.crossingFragment_complete_atGeneratorCountZero

-- FROB-10 P3: the two verdicts (WIRE x2 / WALL x2)
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasCrossingCanonicityImport
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasCrossingRerunAssembly
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasRowLevelSuffixCongruence
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasCrossingPartitionPermutationBridge

-- FROB-10 P4: the completion ledger
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasCrossingRerunLedger

end FX1PolyAudit
