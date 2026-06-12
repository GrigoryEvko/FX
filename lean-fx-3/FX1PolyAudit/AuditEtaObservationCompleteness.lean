import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaObservationCompleteness

/-! # FX1PolyAudit/AuditEtaObservationCompleteness — ETA-T6 inc-1 shard

Per-declaration zero-axiom gate for the observation-completeness
certificate: the containment/scrutinizes checkers, the ★ canonical
table pin, and the extraction chain down to the consumable
per-destructor observation witness.  Must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The canonical pin -/

#assert_no_axioms FX1Poly.Core.etaRuleTable_observationsComplete

/-! ## Extraction -/

#assert_no_axioms FX1Poly.Core.observationsContainObserverHead_extract
#assert_no_axioms FX1Poly.Core.scrutineeListScrutinizes_ofMember
#assert_no_axioms FX1Poly.Core.allRawObservationsCoverIotaDestructors_extract

end FX1PolyAudit
