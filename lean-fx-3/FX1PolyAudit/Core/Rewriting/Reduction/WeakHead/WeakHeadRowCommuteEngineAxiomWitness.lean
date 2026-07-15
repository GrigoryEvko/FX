import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadRowCommuteEngine

/-! # FX1PolyAudit.Core.Rewriting.Reduction.WeakHead.WeakHeadRowCommuteEngineAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the table-generic
row-commute engine: the refire-exposed keystone, the `IotaHeadStep` packaging, and the sixteen
per-row subsumption pins.  Each must print "does not depend on any axioms".  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Core.rowFiringCommuteWithStepRefire
#print axioms FX1Poly.Core.rowFiringCommuteWithStepToIotaHead
#print axioms FX1Poly.Core.boolTrueRedexCommuteWithStep
#print axioms FX1Poly.Core.boolFalseRedexCommuteWithStep
#print axioms FX1Poly.Core.fstPairRedexCommuteWithStep
#print axioms FX1Poly.Core.sndPairRedexCommuteWithStep
#print axioms FX1Poly.Core.natElimZeroRedexCommuteWithStep
#print axioms FX1Poly.Core.natRecZeroRedexCommuteWithStep
#print axioms FX1Poly.Core.listElimNilRedexCommuteWithStep
#print axioms FX1Poly.Core.optionMatchNoneRedexCommuteWithStep
#print axioms FX1Poly.Core.optionMatchSomeRedexCommuteWithStep
#print axioms FX1Poly.Core.eitherMatchInlRedexCommuteWithStep
#print axioms FX1Poly.Core.eitherMatchInrRedexCommuteWithStep
#print axioms FX1Poly.Core.natElimSuccRedexCommuteWithStep
#print axioms FX1Poly.Core.natRecSuccRedexCommuteWithStep
#print axioms FX1Poly.Core.listElimConsRedexCommuteWithStep
#print axioms FX1Poly.Core.idJReflRedexCommuteWithStep
#print axioms FX1Poly.Core.idStrictRecReflRedexCommuteWithStep

end FX1PolyAudit
