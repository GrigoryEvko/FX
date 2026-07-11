import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.CyclicThreeAnickChains

/-! # FX1PolyAudit/Polygraph/Homology/CyclicThreeAnickChains — zero-axiom gate (the ANICK minimal chains
    of the single-letter monomial walkers: the marked-occurrence carrier + decidable minimal-overlap
    guard, the cyclic-3 2-periodic length census tied to the shipped `PeriodicTower.basisCount`, the
    Squier-truncation inequality `Anick 1 ⊊ Squier 2`, and the crown-inheritance anchor)

Per-declaration zero-axiom gate for TOWER-ANICK r1 (#2144): the hand-rolled `natMaxTwo` / `natEqBool`,
the minimal-overlap guard and its marked-chain wrapper, the deterministic position / tips / length
generators, the truth probes (`ssss` recognised; the non-minimal `{0, 2}` and naive `{0, 1, 2}`
rejected; the genuine 3-chain `s⁶`), the 2-periodic length law and censuses, the ★ tie-in to
`PeriodicTower.basisCount`, the monad five-CP census, the Anick boundary riding the tower, the STRICT
Squier-truncation `1 < 2`, and the crown-inheritance finiteness anchor.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.natMaxTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.natEqBool
#assert_no_axioms FX1Poly.Polygraph.Homology.anickMinimalChainTailIsValid
#assert_no_axioms FX1Poly.Polygraph.Homology.isMinimalAnickChain
#assert_no_axioms FX1Poly.Polygraph.Homology.MarkedAnickChain.isMinimal
#assert_no_axioms FX1Poly.Polygraph.Homology.anickChainLastTwoPositions
#assert_no_axioms FX1Poly.Polygraph.Homology.anickChainTips
#assert_no_axioms FX1Poly.Polygraph.Homology.canonicalAnickChain
#assert_no_axioms FX1Poly.Polygraph.Homology.markedCyclicThreeTwoChain
#assert_no_axioms FX1Poly.Polygraph.Homology.markedCyclicThreeThreeChain
#assert_no_axioms FX1Poly.Polygraph.Homology.markedCyclicThreeTwoChainIsMinimal
#assert_no_axioms FX1Poly.Polygraph.Homology.nonMinimalOverlapWidthOneIsRejected
#assert_no_axioms FX1Poly.Polygraph.Homology.naiveDegreeThreeOverlapIsRejected
#assert_no_axioms FX1Poly.Polygraph.Homology.markedCyclicThreeThreeChainIsMinimal
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeThreeChainTipsAreZeroOneThree
#assert_no_axioms FX1Poly.Polygraph.Homology.canonicalCyclicThreeChainPassesGuard
#assert_no_axioms FX1Poly.Polygraph.Homology.anickChainWordLength
#assert_no_axioms FX1Poly.Polygraph.Homology.anickChainWordLengthsThroughDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.anickChainWordLengthIsTwoPeriodic
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeAnickWordLengthsThroughDegreeSix
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeAnickWordLengthsThroughDegreeEight
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeAnickWordLengthMatchesPositions
#assert_no_axioms FX1Poly.Polygraph.Homology.anickChainCountAtDegree
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeAnickChainCountMatchesPeriodicTowerBasis
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionAnickWordLengthsThroughDegreeFive
#assert_no_axioms FX1Poly.Polygraph.Homology.idempotentAnickWordLengthsEqualInvolution
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionAnickWordLengthMatchesPositions
#assert_no_axioms FX1Poly.Polygraph.Homology.walkingMonadSquierCriticalPairCountIsFive
#assert_no_axioms FX1Poly.Polygraph.Homology.walkingMonadAnickCensusIsNamedFutureNode
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeAnickTwoChainBoundaryColumnIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeAnickTwoChainBoundaryMatchesPeriodicTower
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeAnickBoundaryComposesToZeroViaTower
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeAnickTwoChainCountIsOne
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeAnickTwoChainCountStrictlyBelowSquier
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeAnickLengthsSkipFive
#assert_no_axioms FX1Poly.Polygraph.Homology.involutionAnickCountEqualsSquier
#assert_no_axioms FX1Poly.Polygraph.Homology.idempotentAnickCountEqualsSquier
#assert_no_axioms FX1Poly.Polygraph.Homology.anickPerDegreeCountIsFinite
#assert_no_axioms FX1Poly.Polygraph.Homology.anickCrownInheritanceStaysScoped
#assert_no_axioms FX1Poly.Polygraph.Homology.towerAnickRoundOneLedgerIsComplete

end FX1PolyAudit
