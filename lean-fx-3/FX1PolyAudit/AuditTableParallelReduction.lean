import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.TableParallelReduction
import FX1Poly.Core.TableParallelSubstitution

/-! # FX1PolyAudit/AuditTableParallelReduction — IOTA-T6 audit shard (the relation + sandwich + equivariance)

Per-declaration zero-axiom gate for the table-driven parallel reduction:
the mutual relation, reflexivity, the lower sandwich bound (a single
table step is a parallel step), the generic chain homomorphism, the
upper sandwich bound (a parallel step is a finite single-step chain),
and the equivariance engines (single-substitution closure, rename and
weakening corollaries, the interpreter's depth engines, pointwise
substitution relatedness, the diagonal substitution lemma, and the
`subst0`/`substPair` diagonals).  Every declaration below must be free
of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

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

/-! ## Single-substitution closure + rename/weaken corollaries -/

#assert_no_axioms FX1Poly.Core.ParStepOverTable.subst
#assert_no_axioms FX1Poly.Core.ParStepOverTableChildren.subst
#assert_no_axioms FX1Poly.Core.ParStepOverTable.rename
#assert_no_axioms FX1Poly.Core.ParStepOverTableChildren.rename
#assert_no_axioms FX1Poly.Core.ParStepOverTable.weaken

/-! ## The interpreter's depth-weakening engines -/

#assert_no_axioms FX1Poly.Core.ParStepOverTable.weakenBy
#assert_no_axioms FX1Poly.Core.ParStepOverTable.weakenBodyUnderOneBinderBy
#assert_no_axioms FX1Poly.Core.ParStepOverTable.weakenBodyUnderTwoBindersBy
#assert_no_axioms FX1Poly.Core.ParStepOverTableChildren.weakenSpineBy

/-! ## Pointwise relatedness + the diagonal lemma -/

#assert_no_axioms FX1Poly.Core.RawTermSubst.PointwiseParStepOverTable
#assert_no_axioms FX1Poly.Core.RawTermSubst.lift_pointwiseParStepOverTable
#assert_no_axioms FX1Poly.Core.RawTermSubst.iterateLift_pointwiseParStepOverTable
#assert_no_axioms FX1Poly.Core.ParStepOverTable.substPointwise
#assert_no_axioms FX1Poly.Core.ParStepOverTableChildren.substPointwise

/-! ## The `subst0`/`substPair` diagonals -/

#assert_no_axioms FX1Poly.Core.RawTermSubst.singleton_pointwiseParStepOverTable
#assert_no_axioms FX1Poly.Core.RawTermSubst.cons_pointwiseParStepOverTable
#assert_no_axioms FX1Poly.Core.RawTermSubst.pair_pointwiseParStepOverTable
#assert_no_axioms FX1Poly.Core.ParStepOverTable.subst0_diagonal
#assert_no_axioms FX1Poly.Core.ParStepOverTable.substPair_diagonal

end FX1PolyAudit
