import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.LinearizeFull

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/LinearizeFull — zero-axiom gate (OMEGA-2.5 r1, B2)

Per-declaration `#assert_no_axioms` on the boundary-faithful ν map: `polesOf` / `linearizeFull`, the
projection tie `linearizeFull_top`, `polesOf_length`, the reconstruction/decomposition helpers, the four
one-hole congruences, and the `composeAtFull` homomorphism.  Every declaration must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The ν map + the projection tie + the length invariant
#assert_no_axioms FX1Poly.Polygraph.Omega.polesOf
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_top
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_poles
#assert_no_axioms FX1Poly.Polygraph.Omega.polesOf_length

-- The reconstruction + boundary-decomposition helpers
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_eq_of
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_topCoord_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_poles_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_bsCoord_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_btCoord_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_bs_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_eq_succ

-- The four one-hole congruences
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_vcompCongrLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_vcompCongrRight
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_whiskerLeftCongr
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_whiskerRightCongr

-- The composeAtFull homomorphism (B1 op tied to the ν map)
#assert_no_axioms FX1Poly.Polygraph.Omega.linearizeFull_vcomp_composeAtFull

end FX1PolyAudit
