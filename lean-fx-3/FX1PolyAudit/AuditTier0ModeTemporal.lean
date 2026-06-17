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

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasClassicalTemporalDuality
#assert_no_axioms FX1Poly.Tier0.fxMode_hasTemporalFixpointLaws
#assert_no_axioms FX1Poly.Tier0.fxMode_hasBranchingTime
#assert_no_axioms FX1Poly.Tier0.fxMode_hasLtlDecisionProcedure
#assert_no_axioms FX1Poly.Tier0.fxMode_hasKernelTemporalFibration

end FX1PolyAudit
