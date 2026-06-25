import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.Orders.EtaRpoEmbedding

/-! # FX1PolyAudit.Core.Metatheory.Normalization.Orders.EtaRpoEmbedding

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.Orders.EtaRpoEmbedding`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- StepEtaRootTable.rpoEmbeds: the eta-analogue of the iota embedding IotaHeadStep.rpoEmbeds — every raw
-- eta source RPO-decreases its erasure at iotaGenPrecedence, so the oriented eta root rules join the
-- iota/eta union with NO fresh measure.  (The full ι∪η-step IotaEtaStep.{rpoEmbeds,isStronglyNormalizing}
-- live in their own mirror RawIotaEtaFullStepSN, which this module's theorem feeds.)
#assert_no_axioms FX1Poly.Core.StepEtaRootTable.rpoEmbeds

end FX1PolyAudit
