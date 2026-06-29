import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimGateBranchesBounded

/-! # FX1PolyAudit/.../ElimGateBranchesBounded — zero-axiom gate for the bounded elim-gate branches

Per-declaration zero-axiom gate for the seven fuel-bounded eliminator-congruence branches with shipped bounded
`ObligationsDriftBelow` builders (the SR-WF-TIEOFF elim third's per-generator closers): `fst` / `snd`
unconditionally, `app` / `boolElim` / `natElim` / `natRec` modulo before-usability, `pathApp` modulo the
`.dimensional` residual.  Each must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.fstElimGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.sndElimGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.appElimGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.pathAppElimGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.natElimGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.natRecGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.boolElimGateBranchClosesBounded

end FX1PolyAudit
