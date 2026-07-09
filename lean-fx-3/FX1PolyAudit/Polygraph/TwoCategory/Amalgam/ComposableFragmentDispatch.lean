import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.ComposableFragmentDispatch

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.ComposableFragmentDispatch — zero-axiom gate for the composable
empty-law saturated dispatch (WP-AMALG r9)

Per-declaration zero-axiom gate: the projection invariant (`SaturatedConvOver` over a provably-empty relation
reflects exactly to `TwoCellConvFull`), the reconstructed-signature `DecidableEq` bundle, the generic empty-law
decider (the FREE-7 decision transported through the projection iff), the composability enabler, the composable
dispatch (interface-out and interface-in/out), the real walking-monad walker wrapped at the generic interface, the
concrete `involution +_M monad` dispatch, and the non-vacuity verdicts.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the projection invariant (P1/P2)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.emptyRowsFullCongruence
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedConvOverEmptyRows_toFull
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedConvOverEmptyRows_iff_full

-- the reconstructed-signature decidable-equality bundle
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconstructedSignatureModeDecEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconstructedSignatureModalityDecEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconstructedSignatureTwoCellDecEq

-- the generic empty-law decider + the composability enabler
#assert_no_axioms FX1Poly.Polygraph.Amalgam.decidableSaturatedConvOverReconstructed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedConvOverPushoutRows_empty

-- the composable dispatch (P3)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.combinedDecidableSaturatedConvForRel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.saturatedEmptyRowsPushoutDispatch

-- the real walker wrapped at the generic interface
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadWalkerSaturatedDecider

-- the concrete instance + composability witness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadComponentFreeDecider
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionMonadEmptyRowsDispatch
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionMonadCombinedDeciderIsComposable

-- the non-vacuity verdicts
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairPushoutSeparatingVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairPushoutReflexiveVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadWalkerAssocVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadWalkerFacesVerdict

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasComposableFragmentDispatch

end FX1PolyAudit
