import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderSuffixCongruence

/-! # FX1PolyAudit.Polygraph.TwoCategory.Frobenius.SpiderSuffixCongruence — zero-axiom gate (WP-FROB r6, FROB-6)

Per-declaration zero-axiom gate for the forward `stepWiring` view-functoriality brick and the uniform suffix
congruence: the `StepNodeCorr` base fact, the generic arc-fold view invariant, the four-zone post-step classifier,
the single-atom forward view congruence, the suffix fold, the loops-free reconstruction, the uniform suffix
congruence (word- and table-level), the non-vacuity witnesses, and the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- FROB-6: the correspondence base fact + the generic arc-fold view invariant
#assert_no_axioms FX1Poly.Polygraph.stepNodeCorr_baseSameComp
#assert_no_axioms FX1Poly.Polygraph.stepWiringArcs_viewInvariant

-- FROB-6: the four-zone post-step classifier + the decoded-endpoint correspondence
#assert_no_axioms FX1Poly.Polygraph.stepWiring_boundaryRead_stepNodeCorr
#assert_no_axioms FX1Poly.Polygraph.stepWiring_endpointCorr

-- FROB-6: the single-atom forward view congruence + the suffix fold
#assert_no_axioms FX1Poly.Polygraph.stepWiring_viewCongruence
#assert_no_axioms FX1Poly.Polygraph.processBrauer_viewCongruence

-- FROB-6: the reconstruction + the uniform suffix congruence (word + table level)
#assert_no_axioms FX1Poly.Polygraph.spiderConv_stateViewEq
#assert_no_axioms FX1Poly.Polygraph.spiderConv_suffixCongruence
#assert_no_axioms FX1Poly.Polygraph.spiderConvTable_suffixCongruence

-- FROB-6: the non-vacuity witnesses
#assert_no_axioms FX1Poly.Polygraph.spiderConv_special_suffixComult
#assert_no_axioms FX1Poly.Polygraph.spiderConv_special_suffixCounit
#assert_no_axioms FX1Poly.Polygraph.spiderConv_special_suffixComult_distinct
#assert_no_axioms FX1Poly.Polygraph.spiderConv_special_suffixComult_partitionAgrees

-- FROB-6: the honesty markers (new + the flipped ledger flag)
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderSuffixCongruenceShipped
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderSuffixCongruence

end FX1PolyAudit
