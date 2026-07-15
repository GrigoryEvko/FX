import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadRowCommuteEngine

/-! # FX1PolyAudit.Core.Rewriting.Reduction.WeakHead.WeakHeadRowCommuteEngine

Zero-axiom audit shard mirroring kernel module
`FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadRowCommuteEngine` — the table-generic row-commute
engine (the refire-exposed keystone + the `IotaHeadStep` packaging) and the sixteen per-row
subsumption pins.  Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The engine -/

#assert_no_axioms FX1Poly.Core.rowFiringCommuteWithStepRefire
#assert_no_axioms FX1Poly.Core.rowFiringCommuteWithStepToIotaHead

/-! ## The sixteen per-row subsumption pins -/

#assert_no_axioms FX1Poly.Core.boolTrueRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.boolFalseRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.fstPairRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.sndPairRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.natElimZeroRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.natRecZeroRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.listElimNilRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.optionMatchNoneRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.optionMatchSomeRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.eitherMatchInlRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.eitherMatchInrRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.natElimSuccRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.natRecSuccRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.listElimConsRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.idJReflRedexCommuteWithStep
#assert_no_axioms FX1Poly.Core.idStrictRecReflRedexCommuteWithStep

end FX1PolyAudit
