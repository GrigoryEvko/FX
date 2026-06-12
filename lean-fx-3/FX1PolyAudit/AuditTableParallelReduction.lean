import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.TableParallelReduction

/-! # FX1PolyAudit/AuditTableParallelReduction — IOTA-T6 audit shard (the relation + sandwich)

Per-declaration zero-axiom gate for the table-driven parallel reduction:
the mutual relation, reflexivity, the lower sandwich bound (a single
table step is a parallel step), the generic chain homomorphism, and the
upper sandwich bound (a parallel step is a finite single-step chain).
Every declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The relation -/

#assert_no_axioms FX1Poly.Core.ParStepOverTable
#assert_no_axioms FX1Poly.Core.ParStepOverTableChildren

/-! ## Reflexivity -/

#assert_no_axioms FX1Poly.Core.ParStepOverTable.refl
#assert_no_axioms FX1Poly.Core.ParStepOverTableChildren.refl

/-! ## The lower sandwich bound -/

#assert_no_axioms FX1Poly.Core.StepOverTable.toParStepOverTable
#assert_no_axioms FX1Poly.Core.StepOverTableChildren.toParStepOverTableChildren

/-! ## The upper sandwich bound -/

#assert_no_axioms FX1Poly.Core.ReflTransClosure.map
#assert_no_axioms FX1Poly.Core.ParStepOverTable.toStepClosure
#assert_no_axioms FX1Poly.Core.ParStepOverTableChildren.toChildrenStepClosure

end FX1PolyAudit
