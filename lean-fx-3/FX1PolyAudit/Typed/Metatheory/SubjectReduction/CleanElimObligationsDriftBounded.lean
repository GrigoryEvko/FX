import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.CleanElimObligationsDriftBounded

/-! # FX1PolyAudit/.../CleanElimObligationsDriftBounded — zero-axiom gate for the bounded clean-elim drift

Per-declaration zero-axiom gate for the fuel-bounded `ObligationsDriftBelow` builders of the CLEAN eliminators
(`app` / `pathApp` / `fst` / `snd`) plus the shared child-size witnesses.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.headChildBelowCellSize
#assert_no_axioms FX1Poly.Typed.secondChildBelowCellSize
#assert_no_axioms FX1Poly.Typed.thirdChildBelowCellSize
#assert_no_axioms FX1Poly.Typed.fourthChildBelowCellSize
#assert_no_axioms FX1Poly.Typed.appObligationsDriftUnderArgStepBounded
#assert_no_axioms FX1Poly.Typed.pathAppObligationsDriftUnderArgStepBounded
#assert_no_axioms FX1Poly.Typed.fstObligationsDriftUnderArgStepBounded
#assert_no_axioms FX1Poly.Typed.sndObligationsDriftUnderArgStepBounded

end FX1PolyAudit
