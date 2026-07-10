import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDecisionGen

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDecisionGen — zero-axiom gate (generic decider, INTERIM)

Per-declaration zero-axiom gate for the INTERIM generic decider (POLY-TAB r6 S4, honest partial): the interim
canonicalization, the working generic decider, and the regression continuity witnesses.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  (These are zero-AXIOM but NOT bespoke-free — the
completeness residual is recorded by the constant meta-walk in `MonadBespokeFreeWalk`.) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadSaturatedCanonicalizationGenViaBridge
#assert_no_axioms FX1Poly.Polygraph.Amalgam.decideSaturatedConvOverMonadInterim
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadGenDecidesTrue_assoc_holds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadGenDecidesFalse_faces_holds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadGenAgreesOldOnRegression_holds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxMonad_hasGenericNativeDeciderInterim
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxMonad_hasGenericNativeDecider

end FX1PolyAudit
