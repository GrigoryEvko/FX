import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.IntroObligationsDriftBounded

/-! # FX1PolyAudit/.../IntroObligationsDriftBounded — zero-axiom gate for the bounded intro obligation-drift driver

Per-declaration zero-axiom gate for the fuel-bounded introducer obligation-drift driver
(`obligationReclassifiesUnderSubjectDriftBelow` + `premisesHoldUnderObligationsDriftBelow`, the SR-WF-TIEOFF intro
third's drift core).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.obligationReclassifiesUnderSubjectDriftBelow
#assert_no_axioms FX1Poly.Typed.premisesHoldUnderObligationsDriftBelow

end FX1PolyAudit
