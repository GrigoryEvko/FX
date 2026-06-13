import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.IotaTableOperationalExtension

/-! # FX1PolyAudit/AuditIotaTableOperationalExtension — IOTA-T12 audit shard

Per-declaration zero-axiom gate for the operational-axis profile
extension: the extension VALUE structure, its extended-table accessor,
the confluence-preservation payoff, the empty-extension floor, and the
floor's table identity.  Free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.OperationalAxisExtension
#assert_no_axioms FX1Poly.Core.OperationalAxisExtension.extendedTable
#assert_no_axioms FX1Poly.Core.OperationalAxisExtension.preservesConfluence
#assert_no_axioms FX1Poly.Core.OperationalAxisExtension.floor
#assert_no_axioms FX1Poly.Core.floor_extendedTable_eq

end FX1PolyAudit
