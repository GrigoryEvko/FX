import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompMultiGapSeam

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutVcompMultiGapSeam — zero-axiom gate for the r16 vcomp arm at
genuine multi-gap granularity (WP-AMALG-2 r16, B3)

Per-declaration zero-axiom gate for the multi-gap vcomp seam witness + its slot count, the composed head-prepend
witness + its slot count, the skeleton-share adjudication, and the two honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutVcompMultiGapSeamWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutVcompMultiGapSeamWitness_slotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutVcompThenWhiskerMultiGapWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutVcompThenWhiskerMultiGapWitness_slotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutVcompMultiGapConsumesAlignableSkeleton
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasVcompMultiGapSeam
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_vcompMultiGapFullClosureGatedOnReader

end FX1PolyAudit
