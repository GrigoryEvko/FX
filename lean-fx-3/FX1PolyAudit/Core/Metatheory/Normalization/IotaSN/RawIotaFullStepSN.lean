import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.IotaSN.RawIotaFullStepSN

/-! # FX1PolyAudit.Core.Metatheory.Normalization.IotaSN.RawIotaFullStepSN

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.IotaSN.RawIotaFullStepSN`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Full oriented-ι-reduction SN: lift oriented root-ι SN to the COMPATIBLE CLOSURE of IotaOrientedHeadStep —
-- oriented ι at the root OR inside ANY child context (IotaStep/IotaStepChildren, mirroring
-- Step/StepChildren; the two Phase-Z substituting succ-iotas are excluded, β-imported boundary). The
-- congruence case finally CONSUMES rpo_congruence: an ι step inside child position i changes
-- eraseChildren only at that position (prefix ++ child :: suffix → prefix ++ child' :: suffix, the child
-- RPO-decreasing by IH), and rpo_congruence lifts that to a node RPO-decrease. The here/there spine walk
-- builds the prefix ([] at head, eraseToRose head :: prefix one step in). Proven via the explicit mutual
-- recursor IotaStep.rec (the Step.subst pattern). IotaStep.toStep: sound sub-relation of the live Step.
-- iotaFullStep_wellFounded: the GENUINE oriented-ι SN (not just root), Tait-free (β + substituting succ-ι
-- imported, η shipped separately).
#assert_no_axioms FX1Poly.Core.IotaStep.rpoEmbeds

#assert_no_axioms FX1Poly.Core.IotaStep.toStep

#assert_no_axioms FX1Poly.Core.iotaFullStep_wellFounded

#assert_no_axioms FX1Poly.Core.IotaStep.congSmoke

end FX1PolyAudit
