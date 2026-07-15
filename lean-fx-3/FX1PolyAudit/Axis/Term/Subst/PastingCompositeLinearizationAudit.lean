import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Term.Subst.PastingCompositeLinearization

/-! # FX1PolyAudit.Axis.Term.Subst.PastingCompositeLinearizationAudit — zero-axiom gate for the OMEGA-7 r2 cell leg
(OMEGA-7 r2, B1-B3).

Per-declaration `#assert_no_axioms` on the fragment pasting composite (`pasteAlong` + its two boundary-alignment
lemmas), the substitution-realization action (`composeLinearized`), the genuine-map identification
(`linearizeFull_pasteAlong_eq_composeLinearized` = the rfl-anchor `linearizeFull_vcomp_composeAtFull`), the pasting associativity
discharged via `addCoordinates_assoc` (`linearizeFull_pasteAlong_assoc`), the paired kernel anchor
(`substComposeAssoc_and_pastingAssoc`), and the two non-vacuity witnesses.  This audit twin is what
the Polygraph-side ledger marker `fxOmega7_fragmentPastingCompositeLinearized` flips against (the ledger
cannot import Axis). -/

namespace FX1PolyAudit

-- PastingCompositeLinearization.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.pasteAlong
#assert_no_axioms FX1Poly.Polygraph.Omega.boundarySource_pasteAlong
#assert_no_axioms FX1Poly.Polygraph.Omega.boundaryTarget_pasteAlong
#assert_no_axioms FX1Poly.Polygraph.Omega.composeLinearized
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_pasteAlong_eq_composeLinearized
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_pasteAlong_assoc
#assert_no_axioms FX1Poly.Polygraph.Omega.substComposeAssoc_and_pastingAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.composeLinearized_nonVacuity
#assert_no_axioms FX1Poly.Polygraph.Omega.pasteAlongAssoc_nonVacuity

end FX1PolyAudit
