import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.SteinerArithmeticLedger

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/SteinerArithmeticLedger — zero-axiom gate (OMEGA-2 crown lock)

Per-declaration `#assert_no_axioms` on the crown-brick classifier and every honesty marker (the five
shipped bricks, the r1-complete marker, and the two OPEN residuals for r2/r3), plus the namespace
sweep confirming the whole OMEGA-2 Steiner crown introduces zero axioms. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.OmegaTwoBrick
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaTwoBrick_fold_ne_decider
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_isStrongSteinerShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_isStrongSteinerScopedLoopFreeDirectAtomic
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_linearizeShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_compositionIsAddition
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_crownSoundnessUnconditional
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_decideFreeConvSoundNotComplete
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_omega2R1Complete
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_completenessOpenR3
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_n2AgreementOpenR2
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_omegaThreeHandoffRecorded

-- OMEGA-2 r2 ledger markers (B1 integration + B2 falsifier + the r3 route)
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_adcOfComputadShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_admittedBatteryComputable
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_ddEpsdDischargedPerInstance
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_agreementBatteryEvalLevel
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_omega2R2Complete
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega_completenessRouteNamedR3

end FX1PolyAudit
