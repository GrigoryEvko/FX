import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutReconstructedWordGapSplice

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutReconstructedWordGapSplice — zero-axiom gate
(WP-AMALG-2 r14, Brick B2: the multi-gap gap-EZ splice on the reseat)

Per-declaration zero-axiom gate for the reseat-produced generic per-gap fill (`reconWordGapFill`), the three-gap
layout / splice probe, and the establishment marker. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconWordGapFill
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconWordThreeGapLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconWordThreeGapSplice
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_pushoutNormalFormSpliceShips

end FX1PolyAudit
