import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompSkeletonAlignment

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutVcompSkeletonAlignment — zero-axiom gate for the r17 vcomp arm
shared-middle skeleton alignment (WP-AMALG-2 r17, B3)

Per-declaration zero-axiom gate for the shared-middle slot-count alignment theorem, the whole-vcomp dom↔cod slot
agreement, and the two honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcompMultiGapSharedMiddleSlotCountAligns
#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcompMultiGapWholeSlotCountAgrees
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasVcompSkeletonAlignmentTheorem
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_vcompR14SpliceLandsAtDecisionNotSeam

end FX1PolyAudit
