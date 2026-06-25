import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Temporal

/-! # FX1PolyAudit/AuditTier0ModeTemporal — zero-axiom gate for mode-24

Per-declaration zero-axiom gate for `mode-24` (`FX1Poly/Tier0/Mode/Temporal.lean`): the cycle-indexed stream + the
temporal property combinators, the temporal operators (X/G/F/U), the intuitionistic LTL algebraic laws, and the
markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Cycle-indexed streams + temporal property combinators
#assert_no_axioms FX1Poly.Tier0.atom
#assert_no_axioms FX1Poly.Tier0.notOp
#assert_no_axioms FX1Poly.Tier0.andOp
#assert_no_axioms FX1Poly.Tier0.orOp
#assert_no_axioms FX1Poly.Tier0.impliesOp

-- The temporal operators X / G / F / U
#assert_no_axioms FX1Poly.Tier0.next
#assert_no_axioms FX1Poly.Tier0.globally
#assert_no_axioms FX1Poly.Tier0.eventually
#assert_no_axioms FX1Poly.Tier0.untilOp

-- The LTL algebraic laws (intuitionistic)
#assert_no_axioms FX1Poly.Tier0.globally_distrib_and
#assert_no_axioms FX1Poly.Tier0.eventually_distrib_or
#assert_no_axioms FX1Poly.Tier0.next_distrib_and
#assert_no_axioms FX1Poly.Tier0.globally_implies_now
#assert_no_axioms FX1Poly.Tier0.now_implies_eventually
#assert_no_axioms FX1Poly.Tier0.globally_implies_eventually
#assert_no_axioms FX1Poly.Tier0.untilOp_implies_eventually
#assert_no_axioms FX1Poly.Tier0.eventually_not_implies_not_globally
#assert_no_axioms FX1Poly.Tier0.globally_idempotent

-- The μ/ν fixpoint unfolding laws (discharges hasTemporalFixpointLaws)
#assert_no_axioms FX1Poly.Tier0.temporalAddShift
#assert_no_axioms FX1Poly.Tier0.eventually_fixpoint
#assert_no_axioms FX1Poly.Tier0.globally_fixpoint
#assert_no_axioms FX1Poly.Tier0.untilOp_fixpoint

-- CTL branching time over a transition relation (discharges hasBranchingTime)
#assert_no_axioms FX1Poly.Tier0.ReachableVia
#assert_no_axioms FX1Poly.Tier0.ReachableVia.append
#assert_no_axioms FX1Poly.Tier0.ctlEX
#assert_no_axioms FX1Poly.Tier0.ctlAX
#assert_no_axioms FX1Poly.Tier0.ctlEF
#assert_no_axioms FX1Poly.Tier0.ctlAG
#assert_no_axioms FX1Poly.Tier0.ctlAG_implies_here
#assert_no_axioms FX1Poly.Tier0.ctlHere_implies_EF
#assert_no_axioms FX1Poly.Tier0.ctlAG_unfold
#assert_no_axioms FX1Poly.Tier0.ctlAG_and_distrib
#assert_no_axioms FX1Poly.Tier0.ctlEF_or_distrib
#assert_no_axioms FX1Poly.Tier0.branchingTransition
#assert_no_axioms FX1Poly.Tier0.branching_EX_holds
#assert_no_axioms FX1Poly.Tier0.branching_AX_fails

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasClassicalTemporalDuality
#assert_no_axioms FX1Poly.Tier0.fxMode_hasTemporalFixpointLaws
#assert_no_axioms FX1Poly.Tier0.fxMode_hasBranchingTime
#assert_no_axioms FX1Poly.Tier0.fxMode_hasLtlDecisionProcedure
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKernelTemporalFibration

end FX1PolyAudit
