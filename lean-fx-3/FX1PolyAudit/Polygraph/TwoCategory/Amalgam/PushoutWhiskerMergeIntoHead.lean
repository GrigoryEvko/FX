import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerMergeIntoHead

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWhiskerMergeIntoHead — zero-axiom gate for the r17 cell-level
merge-into-head whisker surgery (WP-AMALG-2 r17, B1)

Per-declaration zero-axiom gate for the cell-level merge convertibility, the whiskerLeft merge arm on a layout body,
the framed two-gap witness + its slot-count probe + the conv probe, and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeft_conv_mergeFrameIntoHead
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeWhiskerLeftMergeLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftMergeTwoGapWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.sFrameMergeTwoGapSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.sFrameMergeTwoGapConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWhiskerMergeIntoHeadCell

end FX1PolyAudit
