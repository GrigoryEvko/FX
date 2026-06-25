import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Equality.Eta.EtaTableCanonicalityFlip

/-! # FX1PolyAudit/AuditEtaTableCanonicalityFlip — ETA-T7 ★ flip shard

Per-declaration zero-axiom gate for the eta canonicality flip: the
re-pointed canonical beta-eta headline metatheory (SR / SN / CR /
unique NF).  The modal/Glue divergence record now lives natively as the
`etaModIntro_tableRefusesRaw` / `etaGlueIntro_tableRefusesRaw` pins
(gated in `AuditStepEtaOverTable`).  Every declaration below must be
free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## ★★ The re-pointed canonical beta-eta headline metatheory -/

#assert_no_axioms FX1Poly.Typed.StepTableBetaEtaRoot.subjectReduction
#assert_no_axioms FX1Poly.Typed.StepTableBetaEtaRoot.subjectReductionStar
#assert_no_axioms FX1Poly.Typed.StepTableBetaEtaRoot.stronglyNormalizingTyped
#assert_no_axioms FX1Poly.Typed.StepTableBetaEtaRoot.confluentTyped
#assert_no_axioms FX1Poly.Typed.StepTableBetaEtaRoot.uniqueNormalFormTyped

end FX1PolyAudit
