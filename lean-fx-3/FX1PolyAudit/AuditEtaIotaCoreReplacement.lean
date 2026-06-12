import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaIotaCoreReplacement

/-! # FX1PolyAudit/AuditEtaIotaCoreReplacement — ETA-T5 inc-2 shard

Per-declaration zero-axiom gate for the single-observation core
replacement: the fresh-variable strengthening refutation, the
fresh-pattern extraction and transfer, the lookup-congruence of
extraction, the weakening lift of table steps, and the ★ replacement
itself.  Must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Fresh-block facts -/

#assert_no_axioms FX1Poly.Core.RawTerm.strengthenBy?_freshVar_isNone
#assert_no_axioms FX1Poly.Core.observerFreshVarsHold_atSlot
#assert_no_axioms FX1Poly.Core.observerFreshVarsHold_ofLookupAgree

/-! ## Lookup congruence and weakening lift -/

#assert_no_axioms FX1Poly.Core.EtaObservationSpec.extractCoreFrom?_congrLookup
#assert_no_axioms FX1Poly.Core.StepOverTable.weakenByLift

/-! ## ★ The single-observation replacement -/

#assert_no_axioms FX1Poly.Core.EtaObservationSpec.extractCoreFrom?_replaceCore

end FX1PolyAudit
