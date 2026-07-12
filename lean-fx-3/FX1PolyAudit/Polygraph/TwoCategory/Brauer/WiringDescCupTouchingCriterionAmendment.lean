import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupTouchingCriterionAmendment

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCupTouchingCriterionAmendment — zero-axiom gate (r51)

Per-declaration zero-axiom gate for the BRAUER r51 documented wall-text amendment (the SEVENTH honest zero-flip): the
corrected-criterion pins (`amendedCriterion_straddleRepresentativeIsCupTouching`,
`amendedCriterion_representativeIsNoBareCup`), the amendment honesty marker, and the machine-checked amended terminal
state re-asserting every flip flag and completeness master stays `false`.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `WellFounded.fix` — the pins
reuse the shipped `straddleRepresentativeIsJamResidue` / `residueIrreducibleCrossingCount` /
`cupTouchingCrossing_notBareCup_b3` and the terminal state is a `rfl`-conjunction.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.amendedCriterion_straddleRepresentativeIsCupTouching
#assert_no_axioms FX1Poly.Polygraph.amendedCriterion_representativeIsNoBareCup
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCupTouchingCriterionAmendment
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_cupTouchingCriterionAmendmentTerminalState

end FX1PolyAudit
