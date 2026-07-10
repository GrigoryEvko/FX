import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.StrategyRegistry

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.StrategyRegistry — zero-axiom gate for the certified strategy
registry + generic dispatch soundness (POLY-TAB r1, P2).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.foundElement_satisfiesPredicate
#assert_no_axioms FX1Poly.Polygraph.Amalgam.CertifiedStrategyEntry
#assert_no_axioms FX1Poly.Polygraph.Amalgam.CertifiedStrategyEntry.certifiedDecider
#assert_no_axioms FX1Poly.Polygraph.Amalgam.CertifiedStrategyEntry.admissibilityCertificate
#assert_no_axioms FX1Poly.Polygraph.Amalgam.certifiedStrategyRegistry
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchStrategy
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchFamily
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchMechanism
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchStrategy_sound
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchFamily_staged_eq_admit
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchFamily_staged_isMonad
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchMechanism_staged_isDelta
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchFamily_idempotent_eq_admit
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchStrategy_refusesNearMiss
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchFamily_nearMiss_none
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchFamily_nearMiss_eq_admit
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchedFamilySeparatesVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchedFamilySeparatesVerdict_holds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxTab_hasCertifiedStrategyRegistry

end FX1PolyAudit
