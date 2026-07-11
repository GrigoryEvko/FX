import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerHeadPrependMultiGap

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWhiskerHeadPrependMultiGap — zero-axiom gate for the r16
multi-gap head-prepend whisker arm (WP-AMALG-2 r16, B2)

Per-declaration zero-axiom gate for the empty-gap inner absorption, the cast-free head-prepend convertibility, the
reflexive layout factorization, the multi-gap `whiskerLeft` arm + its slot-count law, the merge-into-head assoc tower,
the concrete three-slot witness + probe, and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.emptyGapPrependInnerAbsorb
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeft_conv_emptyGapPrepend
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeOfLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeWhiskerLeftMultiGap
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mergeFrameIntoHead
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapDomLayout_mergeFrameIntoHead
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapCodLayout_mergeFrameIntoHead
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftMultiGapWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftMultiGapSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeWhiskerLeftMultiGap_slotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWhiskerHeadPrependMultiGap

end FX1PolyAudit
