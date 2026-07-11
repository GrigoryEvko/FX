import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.FiniteCarrierWalkPigeonhole

/-! # FX1PolyAudit/Polygraph/Homology/FiniteCarrierWalkPigeonhole — zero-axiom gate (the classical
    finite-carrier walk pigeonhole `listOverCarrierRepeats`, r10 named ingredient (i))

Per-declaration zero-axiom gate for TOWER-ANICK r11 (#2144): the three hostile-graph truth-probes, the
definitions (`hasRepeatedVertex`, `countVertexOccurrences`, `removeAllVertexOccurrences`), the
cons-reduction lemmas, `natEqBoolSymm` / `natLeOneOrGeTwo`, the contains / count / removeAll transport
lemmas, the additive length identity `removeAllLengthPlusCount`, the pigeonhole `listOverCarrierRepeats`
itself, the ship-gate witnesses, and the ledger markers.

The `#assert_no_axioms` macro is fuel-based (`DependencyAudit`); as an INDEPENDENT cross-check the
load-bearing theorems are ALSO checked with the core `#print axioms` command (which does not truncate) —
each must report "does not depend on any axioms".

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Truth-probes: the three hostile graphs
#assert_no_axioms FX1Poly.Polygraph.Homology.threeCycleIsNonAcyclicAtSaturatingFuel
#assert_no_axioms FX1Poly.Polygraph.Homology.dagChainIsAcyclicWithVanishingBinaryCensus
#assert_no_axioms FX1Poly.Polygraph.Homology.diamondIsAcyclicWithVanishingBinaryCensus

-- Definitions
#assert_no_axioms FX1Poly.Polygraph.Homology.hasRepeatedVertex
#assert_no_axioms FX1Poly.Polygraph.Homology.countVertexOccurrences
#assert_no_axioms FX1Poly.Polygraph.Homology.removeAllVertexOccurrences

-- Cons-reduction lemmas
#assert_no_axioms FX1Poly.Polygraph.Homology.countConsTrue
#assert_no_axioms FX1Poly.Polygraph.Homology.countConsFalse
#assert_no_axioms FX1Poly.Polygraph.Homology.removeAllConsTrue
#assert_no_axioms FX1Poly.Polygraph.Homology.removeAllConsFalse

-- natEqBool symmetry + the Nat dichotomy
#assert_no_axioms FX1Poly.Polygraph.Homology.natEqBoolSymm
#assert_no_axioms FX1Poly.Polygraph.Homology.natLeOneOrGeTwo

-- contains / count transport
#assert_no_axioms FX1Poly.Polygraph.Homology.consPreservesContains
#assert_no_axioms FX1Poly.Polygraph.Homology.countPositiveImpliesContains
#assert_no_axioms FX1Poly.Polygraph.Homology.countGeTwoImpliesRepeat

-- the additive length identity
#assert_no_axioms FX1Poly.Polygraph.Homology.removeAllLengthPlusCount

-- removeAll membership transport
#assert_no_axioms FX1Poly.Polygraph.Homology.containsRemoveAllImpliesContains
#assert_no_axioms FX1Poly.Polygraph.Homology.repeatRemoveAllImpliesRepeat
#assert_no_axioms FX1Poly.Polygraph.Homology.memRemoveAllImpliesMemAndDistinct

-- the pigeonhole + ship-gate witnesses
#assert_no_axioms FX1Poly.Polygraph.Homology.listOverCarrierRepeats
#assert_no_axioms FX1Poly.Polygraph.Homology.hasRepeatedVertexOnConcreteWalk
#assert_no_axioms FX1Poly.Polygraph.Homology.pigeonholeHoldsOverNonBinaryCarrier

-- the ledger markers
#assert_no_axioms FX1Poly.Polygraph.Homology.generalGraphSoundnessResidualsAfterPigeonhole
#assert_no_axioms FX1Poly.Polygraph.Homology.finiteCarrierWalkPigeonholeIsShipped

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
    macro alone) — each must report "does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.Homology.listOverCarrierRepeats
#print axioms FX1Poly.Polygraph.Homology.removeAllLengthPlusCount
#print axioms FX1Poly.Polygraph.Homology.memRemoveAllImpliesMemAndDistinct
#print axioms FX1Poly.Polygraph.Homology.countGeTwoImpliesRepeat

end FX1PolyAudit
