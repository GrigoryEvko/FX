import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Subst.SubstCellPasting

/-! # FX1PolyAudit.Tier0.Term.Subst.SubstCellPastingAudit — zero-axiom gate for the OMEGA-7 r2 cell leg
(OMEGA-7 r2, B1-B3).

Per-declaration `#assert_no_axioms` on the fragment pasting composite (`pasteAlong` + its two boundary-alignment
lemmas), the substitution-realization action (`substCell`), the genuine-map identification
(`substCell_eq_pasteAlong` = the rfl-anchor `linearizeFull_vcomp_composeAtFull`), the pasting associativity
discharged via `addCoordinates_assoc` (`substCell_assoc`), the paired kernel anchor
(`substCellEqPasteAlong_is_substCompose_assoc`), and the two non-vacuity witnesses.  This audit twin is what
the Polygraph-side ledger marker `fxOmega7_fragmentSubstCellEqPasteAlongReached` flips against (the ledger
cannot import Tier0). -/

namespace FX1PolyAudit

-- SubstCellPasting.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.pasteAlong
#assert_no_axioms FX1Poly.Polygraph.Omega.boundarySource_pasteAlong
#assert_no_axioms FX1Poly.Polygraph.Omega.boundaryTarget_pasteAlong
#assert_no_axioms FX1Poly.Polygraph.Omega.substCell
#assert_no_axioms FX1Poly.Polygraph.Omega.substCell_eq_pasteAlong
#assert_no_axioms FX1Poly.Polygraph.Omega.substCell_assoc
#assert_no_axioms FX1Poly.Polygraph.Omega.substCellEqPasteAlong_is_substCompose_assoc
#assert_no_axioms FX1Poly.Polygraph.Omega.substCellEqPasteAlong_nonVacuity
#assert_no_axioms FX1Poly.Polygraph.Omega.substCell_assoc_nonVacuity

end FX1PolyAudit
