import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.Temporal

/-! # FX1PolyAudit/AuditAxisModeTemporal — zero-axiom gate for mode-24

Per-declaration zero-axiom gate for `mode-24` (`FX1Poly/Axis/Mode/Temporal.lean`): the cycle-indexed stream + the
temporal property combinators, the temporal operators (X/G/F/U), the intuitionistic LTL algebraic laws, and the
markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Cycle-indexed streams + temporal property combinators
#assert_no_axioms FX1Poly.Axis.atom
#assert_no_axioms FX1Poly.Axis.notOp
#assert_no_axioms FX1Poly.Axis.andOp
#assert_no_axioms FX1Poly.Axis.orOp
#assert_no_axioms FX1Poly.Axis.impliesOp

-- The temporal operators X / G / F / U
#assert_no_axioms FX1Poly.Axis.next
#assert_no_axioms FX1Poly.Axis.globally
#assert_no_axioms FX1Poly.Axis.eventually
#assert_no_axioms FX1Poly.Axis.untilOp

-- The LTL algebraic laws (intuitionistic)
#assert_no_axioms FX1Poly.Axis.globally_distrib_and
#assert_no_axioms FX1Poly.Axis.eventually_distrib_or
#assert_no_axioms FX1Poly.Axis.next_distrib_and
#assert_no_axioms FX1Poly.Axis.globally_implies_now
#assert_no_axioms FX1Poly.Axis.now_implies_eventually
#assert_no_axioms FX1Poly.Axis.globally_implies_eventually
#assert_no_axioms FX1Poly.Axis.untilOp_implies_eventually
#assert_no_axioms FX1Poly.Axis.eventually_not_implies_not_globally
#assert_no_axioms FX1Poly.Axis.globally_idempotent

-- The μ/ν fixpoint unfolding laws (discharges hasTemporalFixpointLaws)
#assert_no_axioms FX1Poly.Axis.temporalAddShift
#assert_no_axioms FX1Poly.Axis.eventually_fixpoint
#assert_no_axioms FX1Poly.Axis.globally_fixpoint
#assert_no_axioms FX1Poly.Axis.untilOp_fixpoint

-- CTL branching time over a transition relation (discharges hasBranchingTime)
#assert_no_axioms FX1Poly.Axis.ReachableVia
#assert_no_axioms FX1Poly.Axis.ReachableVia.append
#assert_no_axioms FX1Poly.Axis.ctlEX
#assert_no_axioms FX1Poly.Axis.ctlAX
#assert_no_axioms FX1Poly.Axis.ctlEF
#assert_no_axioms FX1Poly.Axis.ctlAG
#assert_no_axioms FX1Poly.Axis.ctlAG_implies_here
#assert_no_axioms FX1Poly.Axis.ctlHere_implies_EF
#assert_no_axioms FX1Poly.Axis.ctlAG_unfold
#assert_no_axioms FX1Poly.Axis.ctlAG_and_distrib
#assert_no_axioms FX1Poly.Axis.ctlEF_or_distrib
#assert_no_axioms FX1Poly.Axis.branchingTransition
#assert_no_axioms FX1Poly.Axis.branching_EX_holds
#assert_no_axioms FX1Poly.Axis.branching_AX_fails

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasClassicalTemporalDuality
#assert_no_axioms FX1Poly.Axis.fxMode_hasTemporalFixpointLaws
#assert_no_axioms FX1Poly.Axis.fxMode_hasBranchingTime
#assert_no_axioms FX1Poly.Axis.fxMode_hasLtlDecisionProcedure
#assert_no_axioms FX1Poly.Axis.fxMode_hasKernelTemporalFibration

end FX1PolyAudit
