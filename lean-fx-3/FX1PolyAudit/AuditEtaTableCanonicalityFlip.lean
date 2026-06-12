import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.EtaTableCanonicalityFlip

/-! # FX1PolyAudit/AuditEtaTableCanonicalityFlip — ETA-T7 ★ flip shard

Per-declaration zero-axiom gate for the eta canonicality flip + the
modal/Glue gating repair: the shrink-soundness wrapper, the typed
coincidence biconditional, the two official over-firing-repaired
divergence witnesses, and the re-pointed canonical beta-eta headline
metatheory (SR / SN / CR / unique NF).  Every declaration below must
be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The shrink is sound + the typed coincidence -/

#assert_no_axioms FX1Poly.Core.StepEtaRootTable.toBespokeEta
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.bespokeEtaIffCanonicalEta

/-! ## The official divergence record (the repair is real) -/

#assert_no_axioms FX1Poly.Typed.bespokeEtaModalOverFiringRepaired
#assert_no_axioms FX1Poly.Typed.bespokeEtaGlueOverFiringRepaired

/-! ## ★★ The re-pointed canonical beta-eta headline metatheory -/

#assert_no_axioms FX1Poly.Typed.StepTableBetaEtaRoot.subjectReduction
#assert_no_axioms FX1Poly.Typed.StepTableBetaEtaRoot.subjectReductionStar
#assert_no_axioms FX1Poly.Typed.StepTableBetaEtaRoot.stronglyNormalizingTyped
#assert_no_axioms FX1Poly.Typed.StepTableBetaEtaRoot.confluentTyped
#assert_no_axioms FX1Poly.Typed.StepTableBetaEtaRoot.uniqueNormalFormTyped

end FX1PolyAudit
