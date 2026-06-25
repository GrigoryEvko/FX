import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.RuleTables.IotaElimTypedLink

/-! # FX1PolyAudit.Typed.Engine.RuleTables.IotaElimTypedLink

Zero-axiom audit shard mirroring kernel module `FX1Poly.Typed.Engine.RuleTables.IotaElimTypedLink`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.iotaRowsAtElim

#assert_no_axioms FX1Poly.Typed.iotaRowsAtElim_app

#assert_no_axioms FX1Poly.Typed.iotaRowsAtElim_pathApp

#assert_no_axioms FX1Poly.Typed.iotaRowAtAppIsBeta

#assert_no_axioms FX1Poly.Typed.iotaRowAtPathAppIsPathBeta

#assert_no_axioms FX1Poly.Typed.iotaRowCoheresWith

#assert_no_axioms FX1Poly.Typed.typedElimIotaRowsCohere

#assert_no_axioms FX1Poly.Typed.gradedElimIotaRowsCohere

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.tableRedexSubjectReduction

end FX1PolyAudit
