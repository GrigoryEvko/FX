import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Graded

/-! # FX1PolyAudit/AuditTier0ModeGraded — zero-axiom gate for mode-26

Per-declaration zero-axiom gate for `mode-26` (`FX1Poly/Tier0/Mode/Graded.lean`): the graded `!_r` exponential
comonad over the shipped DIM-2 usage grade semiring, the store / identity witnesses, the beneath co-Kleisli
composition, the alongside-vs-beneath distributivity crux (citing the shipped lawful semiring), the witness laws,
and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The graded `!_r` exponential comonad + witnesses
#assert_no_axioms FX1Poly.Tier0.GradedExponential
#assert_no_axioms FX1Poly.Tier0.storeGradedExponential
#assert_no_axioms FX1Poly.Tier0.identityGradedExponential

-- The beneath co-Kleisli composition (coeffect accumulation by `*`)
#assert_no_axioms FX1Poly.Tier0.GradedExponential.gradedCompose

-- The alongside-vs-beneath soundness crux (cites the shipped UsageGrade.left_distrib)
#assert_no_axioms FX1Poly.Tier0.beneathDistributesOverAlongside

-- Witness laws (store graded exponential)
#assert_no_axioms FX1Poly.Tier0.storeGradedExponential_counit_comult
#assert_no_axioms FX1Poly.Tier0.storeGradedExponential_split_leftFactor
#assert_no_axioms FX1Poly.Tier0.storeGradedExponential_split_rightFactor
#assert_no_axioms FX1Poly.Tier0.storeGradedExponential_discard_unit
#assert_no_axioms FX1Poly.Tier0.storeGradedExponential_subsume_refl
#assert_no_axioms FX1Poly.Tier0.storeGradedExponential_gradedCompose_eval

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasGradeSensitiveAction
#assert_no_axioms FX1Poly.Tier0.fxMode_hasGradedDistributiveCoherence
#assert_no_axioms FX1Poly.Tier0.fxMode_hasGradedLaxMonoidal
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSubsumptionTwoCell
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKernelGradedFibration

end FX1PolyAudit
