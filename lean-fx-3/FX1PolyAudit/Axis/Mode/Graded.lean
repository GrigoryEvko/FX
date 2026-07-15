import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.Graded

/-! # FX1PolyAudit/AuditAxisModeGraded — zero-axiom gate for mode-26

Per-declaration zero-axiom gate for `mode-26` (`FX1Poly/Axis/Mode/Graded.lean`): the graded `!_r` exponential
comonad over the shipped DIM-2 usage grade semiring, the store / identity witnesses, the beneath co-Kleisli
composition, the alongside-vs-beneath distributivity crux (citing the shipped lawful semiring), the witness laws,
and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The graded `!_r` exponential comonad + witnesses
#assert_no_axioms FX1Poly.Axis.GradedExponential
#assert_no_axioms FX1Poly.Axis.storeGradedExponential
#assert_no_axioms FX1Poly.Axis.identityGradedExponential

-- The beneath co-Kleisli composition (coeffect accumulation by `*`)
#assert_no_axioms FX1Poly.Axis.GradedExponential.gradedCompose

-- The alongside-vs-beneath soundness crux (cites the shipped UsageGrade.left_distrib)
#assert_no_axioms FX1Poly.Axis.beneathDistributesOverAlongside

-- Witness laws (store graded exponential)
#assert_no_axioms FX1Poly.Axis.storeGradedExponential_counit_comult
#assert_no_axioms FX1Poly.Axis.storeGradedExponential_split_leftFactor
#assert_no_axioms FX1Poly.Axis.storeGradedExponential_split_rightFactor
#assert_no_axioms FX1Poly.Axis.storeGradedExponential_discard_unit
#assert_no_axioms FX1Poly.Axis.storeGradedExponential_subsume_refl
#assert_no_axioms FX1Poly.Axis.storeGradedExponential_gradedCompose_eval

-- The subsumption 2-cell (discharges hasSubsumptionTwoCell)
#assert_no_axioms FX1Poly.Axis.storeGradedExponential_subsume_trans
#assert_no_axioms FX1Poly.Axis.storeGradedExponential_subsume_natural

-- The graded distributive coherence (discharges hasGradedDistributiveCoherence)
#assert_no_axioms FX1Poly.Axis.storeGradedExponential_splitDistribute

-- The grade-sensitive action (discharges hasGradeSensitiveAction)
#assert_no_axioms FX1Poly.Axis.gradeSensitiveBang
#assert_no_axioms FX1Poly.Axis.gradeSensitiveBang_zero
#assert_no_axioms FX1Poly.Axis.gradeSensitiveBang_one
#assert_no_axioms FX1Poly.Axis.gradeSensitiveCounit
#assert_no_axioms FX1Poly.Axis.gradeSensitiveMap
#assert_no_axioms FX1Poly.Axis.gradeSensitiveMap_zero
#assert_no_axioms FX1Poly.Axis.gradeSensitiveCounit_map

-- The graded lax-monoidal structure map
#assert_no_axioms FX1Poly.Axis.storeGradedExponential_laxTensor
#assert_no_axioms FX1Poly.Axis.storeGradedExponential_laxTensor_counit

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasGradeSensitiveAction
#assert_no_axioms FX1Poly.Axis.fxMode_hasGradedDistributiveCoherence
#assert_no_axioms FX1Poly.Axis.fxMode_hasGradedLaxMonoidal
#assert_no_axioms FX1Poly.Axis.fxMode_hasSubsumptionTwoCell
#assert_no_axioms FX1Poly.Axis.fxMode_hasKernelGradedFibration

end FX1PolyAudit
