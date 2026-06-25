import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableOrientedSN

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Iota.IotaTableOrientedSN02

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableOrientedSN` (part 2 of 2).
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.orientedTableChildrenToIotaStepChildren

#assert_no_axioms FX1Poly.Core.orientedTableStepToStep

#assert_no_axioms FX1Poly.Core.StepOverTable.successorOver

#assert_no_axioms FX1Poly.Core.stepOverOrientedTable_wellFounded

#assert_no_axioms FX1Poly.Core.orientedTableStep_isStronglyNormalizing

#assert_no_axioms FX1Poly.Core.orientedTableStep_smoke

end FX1PolyAudit
