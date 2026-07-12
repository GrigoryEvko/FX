import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordAppendReshape

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordAppendReshapeAudit — zero-axiom gate for the
full append-vs-vcomp reshape `permWord (front ++ back) w ~ vcomp (permWord front w) (permWord back w)`
(WP-PROP r16, B1).

Per-declaration `#assert_no_axioms` on every public theorem / pin / marker, PLUS independent (non-fuel)
`#print axioms` on the source-boundary reshape, the full append reshape, the matrix pin, and the marker.  The
project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` closes the gate.  The `private`
`Bool` / `Nat` head-validity helpers are file-local and covered transitively (an axiom check on a public theorem
reports the axioms of all its dependencies, including the private ones). -/

namespace FX1PolyAudit

-- B1a — the back-word source-boundary reshape (the nil-front ingredient).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordSourceReshapeConv

-- B1b — the full append-vs-vcomp reshape (gap (ii) closed) + its matrix-soundness pin + the marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordAppendConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordAppendMatrixShared
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_permWordAppendReshapeShipped

-- Independent (non-fuel) axiom prints on the reshapes, the pin, and the marker.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordSourceReshapeConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordAppendConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordAppendMatrixShared
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_permWordAppendReshapeShipped

end FX1PolyAudit
