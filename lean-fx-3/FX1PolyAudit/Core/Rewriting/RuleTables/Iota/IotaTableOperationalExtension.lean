import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableOperationalExtension

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Iota.IotaTableOperationalExtension

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableOperationalExtension`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.OperationalAxisExtension

#assert_no_axioms FX1Poly.Core.OperationalAxisExtension.extendedTable

#assert_no_axioms FX1Poly.Core.OperationalAxisExtension.preservesConfluence

#assert_no_axioms FX1Poly.Core.OperationalAxisExtension.floor

#assert_no_axioms FX1Poly.Core.floor_extendedTable_eq

end FX1PolyAudit
