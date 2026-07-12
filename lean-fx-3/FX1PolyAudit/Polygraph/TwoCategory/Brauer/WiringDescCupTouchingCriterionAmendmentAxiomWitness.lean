import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupTouchingCriterionAmendment

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCupTouchingCriterionAmendmentAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the BRAUER r51 documented wall-text
amendment: the corrected-criterion pins, the amendment honesty marker, and the machine-checked amended terminal state.
Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.amendedCriterion_straddleRepresentativeIsCupTouching
#print axioms FX1Poly.Polygraph.amendedCriterion_representativeIsNoBareCup
#print axioms FX1Poly.Polygraph.fxBrauer_hasCupTouchingCriterionAmendment
#print axioms FX1Poly.Polygraph.fxBrauer_cupTouchingCriterionAmendmentTerminalState

end FX1PolyAudit
