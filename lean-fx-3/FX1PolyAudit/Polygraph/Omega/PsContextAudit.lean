import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.PsContext

/-! # FX1PolyAudit.Polygraph.Omega.PsContextAudit — zero-axiom gate for the CaTT ps-context checker
(OMEGA-6 r1, B1).

Per-declaration `#assert_no_axioms` on the focus-dimension stack walk (`psFocus`), the decidable ps-judgment
(`psContextCheck`), the four non-vacuity contexts (2-globe disk, horizontal composite, dangling, underflow),
and the four checking theorems (two CHECK `true`, two CHECK `false`). -/

namespace FX1PolyAudit

-- PsContext.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.psFocus
#assert_no_axioms FX1Poly.Polygraph.Omega.psContextCheck
#assert_no_axioms FX1Poly.Polygraph.Omega.twoGlobePsContext
#assert_no_axioms FX1Poly.Polygraph.Omega.horizontalCompositePsContext
#assert_no_axioms FX1Poly.Polygraph.Omega.danglingPsContext
#assert_no_axioms FX1Poly.Polygraph.Omega.underflowPsContext
#assert_no_axioms FX1Poly.Polygraph.Omega.twoGlobePsContext_checks
#assert_no_axioms FX1Poly.Polygraph.Omega.horizontalCompositePsContext_checks
#assert_no_axioms FX1Poly.Polygraph.Omega.danglingPsContext_checksFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.underflowPsContext_checksFalse

end FX1PolyAudit
