import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.IotaSN.RawIotaEtaFullStepSN

/-! # FX1PolyAudit.Core.Metatheory.Normalization.IotaSN.RawIotaEtaFullStepSN

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.IotaSN.RawIotaEtaFullStepSN`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- ★ Leg-3 TERM ENDPOINT: the FULL oriented-ι∪η reduction (root + congruence) is strongly normalizing by
-- ONE RPO, Tait-free.  IotaEtaStep = compatible closure of (IotaOrientedHeadStep ∨ StepEtaRootTable),
-- mirroring the full oriented-ι IotaStep.  IotaEtaStep.rpoEmbeds: root via Or.elim (oriented ι via
-- IotaHeadStep.rpoEmbeds fed the guard, η via StepEtaRootTable.rpoEmbeds, both at iotaGenPrecedence),
-- congruence via rpo_congruence.  iotaEtaFullStep_wellFounded: SN via Subrelation.wf + InvImage.wf over
-- iotaGenRpoWellFounded — the oriented ι/η fragment terminates on its OWN order, NOT through Tait (β +
-- the Phase-Z substituting succ-iotas stay imported).  toIotaEta: both fragments inject at the head.
-- canonicalEtaCongSmoke: non-vacuity (canonical-table η inside a congruence).
#assert_no_axioms FX1Poly.Core.IotaEtaStep.rpoEmbeds

#assert_no_axioms FX1Poly.Core.iotaEtaFullStep_wellFounded

#assert_no_axioms FX1Poly.Core.IotaEtaStep.isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.IotaOrientedHeadStep.toIotaEta

#assert_no_axioms FX1Poly.Core.StepEtaRootTable.toIotaEta

#assert_no_axioms FX1Poly.Core.IotaEtaStep.canonicalEtaCongSmoke

end FX1PolyAudit
