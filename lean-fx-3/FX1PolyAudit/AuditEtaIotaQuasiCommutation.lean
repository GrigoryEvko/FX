import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaIotaQuasiCommutation

/-! # FX1PolyAudit/AuditEtaIotaQuasiCommutation — ETA-T5 inc-4.5a shard

Per-declaration zero-axiom gate for the full mutual quasi-commutation:
the union-star congruence lifts, the ★ term/children structural mutual
dispatching all four quadrants (with the duality oracle), the ★★
table-generic Geser hypothesis, and the ★★ union SN corollary feeding
the abstract `accUnion` engine.  Must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Union-star congruence lifts -/

#assert_no_axioms FX1Poly.Core.unionStarCongOfUnionChildrenStar
#assert_no_axioms FX1Poly.Core.unionStarHereOfUnionStar
#assert_no_axioms FX1Poly.Core.unionStarThereOfUnionStar

/-! ## ★ The mutual quasi-commutation -/

#assert_no_axioms FX1Poly.Core.etaIotaQuasiCommutes
#assert_no_axioms FX1Poly.Core.etaIotaQuasiCommutesChildren

/-! ## ★★ The Geser hypothesis and union SN -/

#assert_no_axioms FX1Poly.Core.quasiCommutesRightOverLeft_ofTables
#assert_no_axioms FX1Poly.Core.accUnionOfTables

end FX1PolyAudit
