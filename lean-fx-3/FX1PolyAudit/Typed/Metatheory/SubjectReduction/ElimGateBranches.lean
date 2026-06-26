import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimGateBranches

/-! # FX1PolyAudit/.../ElimGateBranches — zero-axiom gate

Per-declaration zero-axiom gate for the cell-spine-aligned per-generator branches of the SR-DSL-5 eliminator
congruence gate (`fst` / `snd` / `app` / `pathApp` — the four rows whose emitted cell spine equals their rule
`args` order, so the gate `mkGen` bridge holds definitionally and the args-ordered drift families apply directly).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.fstElimGateBranchCloses
#assert_no_axioms FX1Poly.Typed.sndElimGateBranchCloses
#assert_no_axioms FX1Poly.Typed.appElimGateBranchCloses
#assert_no_axioms FX1Poly.Typed.pathAppElimGateBranchCloses

end FX1PolyAudit
