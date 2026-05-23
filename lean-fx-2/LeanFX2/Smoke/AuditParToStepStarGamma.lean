import LeanFX2.Reduction.StepStarCongLifters
import LeanFX2.Reduction.ParToStepStar

/-! Zero-axiom audit for the StepStar congruence lifters
(`Reduction/StepStarCongLifters`) and the parallel-into-RT-closure
leaf families (`Reduction/ParToStepStar`).

Every `#print axioms` below MUST report "does not depend on any
axioms". -/

namespace LeanFX2

-- Closed-type congruence lifters (value constructors).
#print axioms StepStar.optionSomeValue_lift_general
#print axioms StepStar.optionSomeValue_lift
#print axioms StepStar.eitherInlValue_lift_general
#print axioms StepStar.eitherInlValue_lift
#print axioms StepStar.eitherInrValue_lift_general
#print axioms StepStar.eitherInrValue_lift
#print axioms StepStar.listConsHead_lift_general
#print axioms StepStar.listConsHead_lift
#print axioms StepStar.listConsTail_lift_general
#print axioms StepStar.listConsTail_lift

-- Closed-type congruence lifters (parametric eliminator scrutinees).
#print axioms StepStar.listElimScrutinee_lift_general
#print axioms StepStar.listElimScrutinee_lift
#print axioms StepStar.optionMatchScrutinee_lift_general
#print axioms StepStar.optionMatchScrutinee_lift
#print axioms StepStar.eitherMatchScrutinee_lift_general
#print axioms StepStar.eitherMatchScrutinee_lift

-- Parallel-into-RT-closure leaf families (univalence / funext).
#print axioms Step.par.eqType_toStepStar
#print axioms Step.par.eqArrow_toStepStar
#print axioms Step.par.eqTypeHet_toStepStar
#print axioms Step.par.eqArrowHet_toStepStar

end LeanFX2
