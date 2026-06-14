import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.StepEtaTableBackward

/-! # FX1PolyAudit/AuditStepEtaTableBackward — eta-observation core
extractor audit shard

Per-declaration zero-axiom gate for the generic observation inversion
(the shared substrate the table-native source-shape reader and the
child-join dispatchers build on).  Every declaration below must be free
of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The generic observation inversion -/

#assert_no_axioms FX1Poly.Core.EtaObservationSpec.extractCoreFrom?_someInversion

end FX1PolyAudit
