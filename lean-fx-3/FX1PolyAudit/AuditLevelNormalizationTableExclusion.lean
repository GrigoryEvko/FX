import FX1PolyAudit.DependencyAudit
import FX1Poly.Universe.LevelNormalizationTableExclusion

/-! # FX1PolyAudit/AuditLevelNormalizationTableExclusion — LEVEL-TAB audit shard

Per-declaration zero-axiom gate for the LEVEL-TAB pinned-exclusion bundle:
the candidate `lmaxOrient` orientation, the 2-cycle (`lmaxOrient_cycles`),
the soundness equation (`lmaxOrient_denoteEquiv`), the non-triviality
witness, the denote-equal-but-distinct fact, the ledger value
(`levelNormalizationStatus`), and the ★ exclusion certificate
(`levelNormalization_exclusion_justified`).  Every declaration below must be
free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The orientation + the 2-cycle obstruction -/

#assert_no_axioms FX1Poly.Universe.LevelExpr.lmaxOrient
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmaxOrient_cycles
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmaxOrient_denoteEquiv
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmaxOrient_nontrivial_witness
#assert_no_axioms FX1Poly.Universe.LevelExpr.lmaxOrientations_denoteEquiv_but_distinct

/-! ## The pinned ledger entry -/

#assert_no_axioms FX1Poly.Universe.levelNormalizationStatus
#assert_no_axioms FX1Poly.Universe.levelNormalization_exclusion_justified

end FX1PolyAudit
