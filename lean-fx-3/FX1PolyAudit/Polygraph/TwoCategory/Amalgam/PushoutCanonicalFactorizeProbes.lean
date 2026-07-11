import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCanonicalFactorizeProbes

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutCanonicalFactorizeProbes — zero-axiom gate for the r19
assembled canonical arm status + historical-wild probes + JAM A re-audit (WP-AMALG-2 r19, B4)

Per-declaration zero-axiom gate for the assembled arm status, the gated-arm pins, the historical-wild slot-count
probes, the JAM A re-audit pins, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeCanonicalArmsShipped
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeCanonicalArmsShipped_true
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeCanonicalGatedArmsHeld
#assert_no_axioms FX1Poly.Polygraph.Amalgam.canonicalProbe_wallSplitterDom
#assert_no_axioms FX1Poly.Polygraph.Amalgam.canonicalProbe_wallSplitterCod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.canonicalProbe_composedCodomain
#assert_no_axioms FX1Poly.Polygraph.Amalgam.canonicalProbe_witnessWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.canonicalProbe_allThree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.canonicalProbesJamAOpen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.canonicalProbesNoMasterFlips
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasCanonicalFactorizeProbes
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_canonicalProbesJamAReAudit

end FX1PolyAudit
