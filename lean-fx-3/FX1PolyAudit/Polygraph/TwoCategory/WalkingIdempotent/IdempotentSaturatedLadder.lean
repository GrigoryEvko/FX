import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedLadder

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedLadder — zero-axiom gate

Per-declaration zero-axiom gate for the GENERIC-NATIVE fold/grow ladder (POLY-TAB r4).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.foldThenGrowGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.growThenFoldGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.foldWhiskerStepGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftCanonOneGen

end FX1PolyAudit
