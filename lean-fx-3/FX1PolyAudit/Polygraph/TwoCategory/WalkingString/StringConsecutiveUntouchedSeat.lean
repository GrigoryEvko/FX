import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringConsecutiveUntouchedSeat

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringConsecutiveUntouchedSeat — zero-axiom gate
(FC-3 r25, B1)

Per-declaration zero-axiom gate for the FORWARD adjacency invariant substrate.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- B1 — the forward adjacency-preservation step (a disjoint cap keeps a seated pair seated)
#assert_no_axioms FX1Poly.Polygraph.stringArcPairSeated_stepCapArc_ofDisjointReads

-- B1 — the below-fresh membership monotonicity (the Risk-R1 reverse read-off), per-step + fold
#assert_no_axioms FX1Poly.Polygraph.stringMemStepArcAtom_belowFresh_imp
#assert_no_axioms FX1Poly.Polygraph.stringMemProcessArcSpine_belowFresh_imp

-- B1 — the concrete truth-probe + the honesty marker
#assert_no_axioms FX1Poly.Polygraph.stringConsecutiveUntouchedSeatProbeState
#assert_no_axioms FX1Poly.Polygraph.stringConsecutiveUntouchedSeatProbe_fires
#assert_no_axioms FX1Poly.Polygraph.fxString_hasConsecutiveUntouchedSeatForward

end FX1PolyAudit
