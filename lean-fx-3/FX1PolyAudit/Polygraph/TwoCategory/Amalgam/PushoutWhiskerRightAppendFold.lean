import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightAppendFold

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightAppendFold — zero-axiom gate for LEG 1: the
`whiskerRight` trailing-frame append CONS-CASE fold (WP-AMALG-2 r18, B3)

Per-declaration zero-axiom gate for the reusable right-factor cast-pull `hcomp_conv_castBoundaryRight`, the full
trailing-append fold `whiskerRight_conv_appendFinalWall` (the r17 leg-1 residual, now shipped), and the honesty
marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.hcomp_conv_castBoundaryRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRight_conv_appendFinalWall
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWhiskerRightAppendCell

end FX1PolyAudit
