import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeCanonicalWhiskerRight

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFactorizeCanonicalWhiskerRight — zero-axiom gate for the r18
canonical `whiskerRight` merge-layout arm + the wild probes + the JAM A re-audit (WP-AMALG-2 r18, B4)

Per-declaration zero-axiom gate for the canonical whiskerRight arm `pushoutFactorizeWhiskerRightMergeLayout`, the
two-gap and wire-changing right-merge witnesses + slot-count probes, the wall-free spec-agreement probe, the master +
JAM A pins, and the three honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeWhiskerRightMergeLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightMergeTwoGapWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightMergeTwoGapSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muBlockRightFrameWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muBlockRightFrameSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.genMeetsCanonicalSlotSpec
#assert_no_axioms FX1Poly.Polygraph.Amalgam.canonicalWhiskerRightArmNoMasterFlips
#assert_no_axioms FX1Poly.Polygraph.Amalgam.canonicalWhiskerRightArmJamAOpen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasCanonicalWhiskerRightArm
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_canonicalReaderJamAReAuditR18
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_totalCanonicalReaderStaysGated

end FX1PolyAudit
