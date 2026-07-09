import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.DeciderReseat

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.DeciderReseat — zero-axiom gate for the reconstruction bridge (P3)
and the cross-component separation witness (P4) (WP-AMALG r6)

Per-declaration zero-axiom gate: the pushout monad unit + faces, the interleaving cross-component pair, the
boundary block-decompositions (each `rfl`), the monad-block separation (via the shipped bespoke decision), the
convertible isTrue counterpart, and the P3 0/1-skeleton reconstruction graph equivalence.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- P4: pushout monad unit + faces
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadPushMode
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadPushSModality
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadPushTModality
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadPushSPath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadPushTPath
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutMonadUnit
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutEta
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFaceDeltaOne
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFaceDeltaZero

-- P4: the genuinely interleaving cross-component pair
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairAlpha
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairBeta

-- P4: boundary words + their block decompositions (each rfl)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairDomainWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairCodomainWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairDomainDecompose
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairCodomainDecompose
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairDomainAlternates
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPair_sharedPrefix

-- P4: the monad-block separation + convertible counterpart
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairMonadBlocksSeparate
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairConvertibleCounterpart

-- P3: the 0/1-skeleton reconstruction graph equivalence
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadFinToMode
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadModeToFin
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadComputadModeEquiv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finOneEqZero
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadModalityEqT
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadComputadModalityEquiv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadComputadGraphEquiv

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasReconstructionGraphBridge
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasReconstructionDecoderReseat
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasCrossComponentSeparationWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasLiveMonadPushoutIsFalse

end FX1PolyAudit
