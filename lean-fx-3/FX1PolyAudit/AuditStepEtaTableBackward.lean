import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.StepEtaTableBackward

/-! # FX1PolyAudit/AuditStepEtaTableBackward — ETA-T1 audit shard
(increment B)

Per-declaration zero-axiom gate for the backward eta adequacy: the
generic observation inversion, the three per-row backward firing
inversions, and the total root backward (raw-tier table contractions
ARE the bespoke eta).  Every declaration below must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

/-! ## The generic observation inversion -/

#assert_no_axioms FX1Poly.Core.EtaObservationSpec.extractCoreFrom?_someInversion

/-! ## The per-row backward inversions -/

#assert_no_axioms FX1Poly.Core.etaLamRowContractionToBespokeEta
#assert_no_axioms FX1Poly.Core.etaPathLamRowContractionToBespokeEta
#assert_no_axioms FX1Poly.Core.etaPairRowContractionToBespokeEta

/-! ## ★ The total root backward -/

#assert_no_axioms FX1Poly.Core.stepEtaTableRootToBespokeEta

end FX1PolyAudit
