import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDecisionGen

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDecisionGen — zero-axiom gate (generic decider markers)

Per-declaration zero-axiom gate for the surviving generic-decider markers.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.

MONAD-R7 r2 (S5) RETIRED the INTERIM decider (`monadSaturatedCanonicalizationGenViaBridge` /
`decideSaturatedConvOverMonadInterim` + its `monadGenDecidesTrue_assoc` / `monadGenDecidesFalse_faces` /
`monadGenAgreesOldOnRegression` regression witnesses), so their per-declaration `#assert_no_axioms` gates are gone
with them; the interim milestone is now recorded historically (the `fxMonad_hasGenericNativeDeciderInterim` marker
and `Table/TableRetirementLedger`).  The fully bespoke-free native decider `decideSaturatedConvOverMonadNative` and its
completeness/soundness legs are gated in `WalkingMonad/MonadNormalizeGen`'s audit twin and the bespoke-free
meta-walk `MonadBespokeFreeWalk`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxMonad_hasGenericNativeDeciderInterim
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxMonad_hasGenericNativeDecider

end FX1PolyAudit
