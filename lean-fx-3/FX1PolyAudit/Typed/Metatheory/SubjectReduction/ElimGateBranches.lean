import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimGateBranches

/-! # FX1PolyAudit/.../ElimGateBranches — zero-axiom gate

Per-declaration zero-axiom gate for ALL ELEVEN per-generator branches of the SR-DSL-5 eliminator congruence gate:

  * the four base rows (`fst` / `snd` / `app` / `pathApp`) and the five dependent rows whose scrutinee/witness is
    last in BOTH `args` and cell spine (`optionMatch` / `eitherMatch` / `natElim` / `natRec` / `idJ`) — cell-spine
    aligned, so the gate `mkGen` bridge holds definitionally and the args-ordered drift families apply directly;
  * the two cell-spine-permuting rows (`boolElim` / `listElim`, scrutinee at `args` position 1 but last in the
    spine) — rebuilt via the spine-aligned reindex.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.fstElimGateBranchCloses
#assert_no_axioms FX1Poly.Typed.sndElimGateBranchCloses
#assert_no_axioms FX1Poly.Typed.appElimGateBranchCloses
#assert_no_axioms FX1Poly.Typed.pathAppElimGateBranchCloses
#assert_no_axioms FX1Poly.Typed.boolElimGateBranchCloses
#assert_no_axioms FX1Poly.Typed.optionMatchGateBranchCloses
#assert_no_axioms FX1Poly.Typed.eitherMatchGateBranchCloses
#assert_no_axioms FX1Poly.Typed.natElimGateBranchCloses
#assert_no_axioms FX1Poly.Typed.natRecGateBranchCloses
#assert_no_axioms FX1Poly.Typed.idJGateBranchCloses
#assert_no_axioms FX1Poly.Typed.listElimGateBranchCloses

end FX1PolyAudit
