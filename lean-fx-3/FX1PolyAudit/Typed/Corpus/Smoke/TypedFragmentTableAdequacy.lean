import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Corpus.Smoke.TypedFragmentTableAdequacy

/-! # FX1PolyAudit.Typed.Corpus.Smoke.TypedFragmentTableAdequacy

Zero-axiom audit shard mirroring kernel module `FX1Poly.Typed.Corpus.Smoke.TypedFragmentTableAdequacy`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.StepOverTable.invertOrCong

#assert_no_axioms FX1Poly.Typed.tableAvoidsElimHead

#assert_no_axioms FX1Poly.Typed.tableAvoidsElimHead_var

#assert_no_axioms FX1Poly.Typed.tableAvoidsElimHead_lam

#assert_no_axioms FX1Poly.Typed.tableAvoidsElimHead_universeCode

#assert_no_axioms FX1Poly.Typed.noRowEliminatesAvoidedHead

#assert_no_axioms FX1Poly.Typed.tableElimHeadsLackTypingRows

#assert_no_axioms FX1Poly.Typed.elimRowHeadHasNoTypingRule

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.tableStepToStep

#assert_no_axioms FX1Poly.Typed.HasTypeDesc.tableStepToStep

#assert_no_axioms FX1Poly.Typed.DescTelescopePi.tableChildrenStepToStepChildren

#assert_no_axioms FX1Poly.Typed.DescTelescope.tableChildrenStepToStepChildren

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionTable

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionTableStar

end FX1PolyAudit
