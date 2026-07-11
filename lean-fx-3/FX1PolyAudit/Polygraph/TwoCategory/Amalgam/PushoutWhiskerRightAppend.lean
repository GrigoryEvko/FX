import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightAppend

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightAppend — zero-axiom gate for the r17 `whiskerRight`
trailing-frame append machinery (WP-AMALG-2 r17, B2)

Per-declaration zero-axiom gate for the new dual cast lemma `whiskerRightCastBoundaryEq`, the hcomp right-push engine
`whiskerRight_conv_hcompRight`, the trailing-frame distribution inductions `gapDomLayoutAppendFinalWall` /
`gapCodLayoutAppendFinalWall`, the append base case `whiskerRight_conv_appendFinalWall_nil`, the concrete two-gap
distribution probe `sFrameAppendTwoGapDistributes`, and the two honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightCastBoundaryEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRight_conv_hcompRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapDomLayoutAppendFinalWall
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapCodLayoutAppendFinalWall
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRight_conv_appendFinalWall_nil
#assert_no_axioms FX1Poly.Polygraph.Amalgam.sFrameAppendTwoGapDistributes
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWhiskerRightAppendEngine
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_sFrameWallShiftStaysWalled

end FX1PolyAudit
