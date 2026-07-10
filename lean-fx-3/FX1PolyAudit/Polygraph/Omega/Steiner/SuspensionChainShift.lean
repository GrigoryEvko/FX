import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.SuspensionChainShift

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/SuspensionChainShift — zero-axiom gate (OMEGA-3 r2, B4).

Per-declaration `#assert_no_axioms` on the suspension chain-table shift: the append-one-bottom-pole helper
and its length, the pole-table shift (`polesOf_suspend`, whose dimension-0 base inverts a suspended
zero-cell), the full-table shift, and the extra-bottom-pole non-vacuity. -/

namespace FX1PolyAudit

-- SuspensionChainShift.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.appendBottomPole
#assert_no_axioms FX1Poly.Polygraph.Omega.appendBottomPole_length
#assert_no_axioms FX1Poly.Polygraph.Omega.polesOf_suspend
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_suspend
#assert_no_axioms FX1Poly.Polygraph.Omega.suspend_polesOf_length_succ

end FX1PolyAudit
