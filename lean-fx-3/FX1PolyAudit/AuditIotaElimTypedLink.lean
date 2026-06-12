import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.IotaElimTypedLink
import FX1Poly.Typed.TypedFragmentTableAdequacy

/-! # FX1PolyAudit/AuditIotaElimTypedLink — IOTA-T7 audit shard (the typed link)

Per-declaration zero-axiom gate for the static↔operational pairing (row
filters, dispatch bricks, coherence gates), the generic typed
table-redex subject reduction, the typed-fragment table adequacy, and
the full-table master subject reduction.  Every declaration below must
be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Row filters + dispatch bricks -/

#assert_no_axioms FX1Poly.Typed.iotaRowsAtElim
#assert_no_axioms FX1Poly.Typed.iotaRowsAtElim_app
#assert_no_axioms FX1Poly.Typed.iotaRowsAtElim_pathApp
#assert_no_axioms FX1Poly.Typed.iotaRowAtAppIsBeta
#assert_no_axioms FX1Poly.Typed.iotaRowAtPathAppIsPathBeta

/-! ## The coherence gates -/

#assert_no_axioms FX1Poly.Typed.iotaRowCoheresWith
#assert_no_axioms FX1Poly.Typed.typedElimIotaRowsCohere
#assert_no_axioms FX1Poly.Typed.gradedElimIotaRowsCohere

/-! ## The generic typed table-redex SR + the legacy seam -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.tableRedexSubjectReduction
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionOverLegacyTable
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionStarOverLegacyTable

/-! ## The freed-subject table-step inversion + rigidity checkers -/

#assert_no_axioms FX1Poly.Core.StepOverTable.invertOrCong
#assert_no_axioms FX1Poly.Typed.tableAvoidsElimHead
#assert_no_axioms FX1Poly.Typed.tableAvoidsElimHead_var
#assert_no_axioms FX1Poly.Typed.tableAvoidsElimHead_lam
#assert_no_axioms FX1Poly.Typed.tableAvoidsElimHead_universeCode
#assert_no_axioms FX1Poly.Typed.noRowEliminatesAvoidedHead
#assert_no_axioms FX1Poly.Typed.tableElimHeadsLackTypingRows
#assert_no_axioms FX1Poly.Typed.elimRowHeadHasNoTypingRule

/-! ## The typed-fragment collapse -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.tableStepToStep
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.tableStepToStep
#assert_no_axioms FX1Poly.Typed.DescTelescopePi.tableChildrenStepToStepChildren
#assert_no_axioms FX1Poly.Typed.DescTelescope.tableChildrenStepToStepChildren

/-! ## ★★ The full-table master subject reduction -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionTable
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionTableStar

end FX1PolyAudit
