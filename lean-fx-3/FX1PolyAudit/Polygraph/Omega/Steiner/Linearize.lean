import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.Linearize

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/Linearize — zero-axiom gate (OMEGA-2 B2 + B3)

Per-declaration `#assert_no_axioms` on the ν/basis map: the valuation, `linearize`, the six
computation lemmas (the homomorphism legs), the length invariant, and the `composeAtDimension`
connection.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ComputadValuation
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_ofMode
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_gen
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_id
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_vcomp
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_length
#assert_no_axioms FX1Poly.Polygraph.Omega.linearize_vcomp_composeAt

end FX1PolyAudit
