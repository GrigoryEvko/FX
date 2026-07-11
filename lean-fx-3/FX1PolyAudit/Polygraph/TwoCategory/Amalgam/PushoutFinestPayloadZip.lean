import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestPayloadZip

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFinestPayloadZip — zero-axiom gate for the payload zip's
aligned TARGET (the vcomp seam at the finest common refinement + the r8-shape skeleton alignment, WP-AMALG-2 r13)

Per-declaration zero-axiom gate for the seam-at-finest, the all-boundary legality certificate, the r8 middle 1-cell,
the r8 skeleton alignment self-attack, the seam-at-finest reflexive non-vacuity probe, and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeVcompSeamFinest
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestLayoutPresentsAllBoundaries
#assert_no_axioms FX1Poly.Polygraph.Amalgam.r8MiddleOneCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestLayoutAlignsR8Shape
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeVcompSeamFinestReflProbe
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFinestSeamZipCorollary

end FX1PolyAudit
