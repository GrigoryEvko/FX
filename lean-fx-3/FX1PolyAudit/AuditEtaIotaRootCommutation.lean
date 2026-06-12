import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaIotaRootCommutation

/-! # FX1PolyAudit/AuditEtaIotaRootCommutation — ETA-T5 inc-3 shard

Per-declaration zero-axiom gate for the root-eta quasi-commutation:
the star prepend and spine star, the agreement-gate extraction and
re-assembly, the richer contraction inversion, the replacement chain,
and the ★ root-eta case — plus the WfEtaTable extension (the
pairwise-distinct observation-slot checker and the re-decided 5-field
canonical certificate).  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The WfEtaTable extension -/

#assert_no_axioms FX1Poly.Core.rowObservationSlotsDistinct
#assert_no_axioms FX1Poly.Core.allObservationSlotsDistinct
#assert_no_axioms FX1Poly.Core.etaRuleTable_isWf

/-! ## Star machinery -/

#assert_no_axioms FX1Poly.Core.UnionStar.headLeft
#assert_no_axioms FX1Poly.Core.unionStarCongOfChildrenStar

/-! ## Agreement extraction and re-assembly -/

#assert_no_axioms FX1Poly.Core.etaObservationsAgree_memberExtracts
#assert_no_axioms FX1Poly.Core.etaObservationsAgree_ofAllExtract
#assert_no_axioms FX1Poly.Core.EtaRuleDesc.contractsOn?_consInversion
#assert_no_axioms FX1Poly.Core.EtaRuleDesc.contractsOn?_ofExtracts

/-! ## The chain and ★ the root-eta case -/

#assert_no_axioms FX1Poly.Core.replaceCoresAlongObservations
#assert_no_axioms FX1Poly.Core.etaRedexQuasiCommutesOverIota

end FX1PolyAudit
