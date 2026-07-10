import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapBlockGodementStep

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringCapBlockGodementStep — zero-axiom gate (FC-3 r10, B3)

Per-declaration zero-axiom gate for the positive-core opening: the cap-block Godement chain's trace-equivalence lift
(`stringCapBlockGodementChain_spineTraceEquiv`), the keystone-driven base case
(`stringWordChainedSingletonBlock_eq_of_readOffs`), the non-vacuity witness
(`stringCapBlockGodementStep_nonvacuity`), and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringCapBlockGodementChain_spineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.stringWordChainedSingletonBlock_eq_of_readOffs
#assert_no_axioms FX1Poly.Polygraph.stringCapBlockGodementStep_nonvacuity
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCapBlockGodementStepOpening

end FX1PolyAudit
