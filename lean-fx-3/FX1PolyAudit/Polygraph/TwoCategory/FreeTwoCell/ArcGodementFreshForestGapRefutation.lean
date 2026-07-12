import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcGodementFreshForestGapRefutation

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcGodementFreshForestGapRefutation — zero-axiom gate

Per-declaration zero-axiom gate for the FOREST-GAP adjudication (r21, branch (a)): the fresh-but-cyclic
counterexample is `ArcStateFresh` (`arcFreshCyclicForestGapState_isFresh`) yet NOT a union-find forest
(`arcFreshCyclicForestGapLinks_notForest` / `arcFreshCyclicForestGapState_notForest`), its boundary width fits
(`bottomCountBelowFresh`), the two Godement run orders' internal CAP-event counts at port `0` DIVERGE
(`internalCapCountAtPortZero_differs`), and hence the LITERAL fresh residual is FALSE
(`not_arcGodementSamePartitionFresh`).  Plus the honesty marker and the two graveyard pins: the :472-pin
`fxMode_hasArcGodementSamePartitionFreshProof` and the corrected-target-closure marker
`fxMode_hasArcForestFreshResidualClosed` both stay `false` (re-asserted by `rfl`).

The file flips ONLY its own NEW marker `fxMode_hasArcGodementSamePartitionFreshRefuted := true` (the literal is
REFUTED); it introduces NO new residual definition — the corrected target `ArcGodementSamePartitionFreshForest`
already ships in `ArcFreshGatedPartitionCommute`.

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the two
are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- the counterexample: fresh, non-forest, boundary width fits
#assert_no_axioms FX1Poly.Polygraph.arcFreshCyclicForestGapState_isFresh
#assert_no_axioms FX1Poly.Polygraph.arcFreshCyclicForestGapLinks_notForest
#assert_no_axioms FX1Poly.Polygraph.arcFreshCyclicForestGapState_notForest
#assert_no_axioms FX1Poly.Polygraph.bottomCountBelowFresh

-- the decided divergence + the refutation
#assert_no_axioms FX1Poly.Polygraph.internalCapCountAtPortZero_differs
#assert_no_axioms FX1Poly.Polygraph.not_arcGodementSamePartitionFresh

-- honesty marker + graveyard pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcGodementSamePartitionFreshRefuted
#assert_no_axioms FX1Poly.Polygraph.arcGodementFreshForestGapRefutation_samePartitionFreshProof_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcGodementFreshForestGapRefutation_forestResidualClosed_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.arcFreshCyclicForestGapState_isFresh
#print axioms FX1Poly.Polygraph.arcFreshCyclicForestGapLinks_notForest
#print axioms FX1Poly.Polygraph.arcFreshCyclicForestGapState_notForest
#print axioms FX1Poly.Polygraph.bottomCountBelowFresh
#print axioms FX1Poly.Polygraph.internalCapCountAtPortZero_differs
#print axioms FX1Poly.Polygraph.not_arcGodementSamePartitionFresh
#print axioms FX1Poly.Polygraph.fxMode_hasArcGodementSamePartitionFreshRefuted
#print axioms FX1Poly.Polygraph.arcGodementFreshForestGapRefutation_samePartitionFreshProof_stays_false
#print axioms FX1Poly.Polygraph.arcGodementFreshForestGapRefutation_forestResidualClosed_stays_false

end FX1PolyAudit
