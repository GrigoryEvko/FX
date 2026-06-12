import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaIotaCongRootAssembly

/-! # FX1PolyAudit/AuditEtaIotaCongRootAssembly — ETA-T5 inc-4.4c shard

Per-declaration zero-axiom gate for the cong-eta-before-root-iota
quadrant: the union-star right-prepend and eta-star embedding bricks
plus the ★ assembly theorem (fronted iota + right-only star, or the
duality witness).  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Union-star bricks -/

#assert_no_axioms FX1Poly.Core.UnionStar.headRight
#assert_no_axioms FX1Poly.Core.StepEtaOverTableStar.toUnionStarRight

/-! ## ★ The assembly -/

#assert_no_axioms FX1Poly.Core.congEtaQuasiCommutesOverRootIota

end FX1PolyAudit
