import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.CrossedModuleRelationModule

/-! # FX1PolyAudit/Polygraph/Homology/CrossedModuleRelationModule — zero-axiom gate (the relation-module
    characterization of the free crossed module of `⟨s | s³⟩`: kernel landing, realization surjection,
    the injectivity-wall adjudication, and the H2 tie)

Per-declaration zero-axiom gate for WP-2GROUP r3 (#2199): the augmentation / norm element and the target
lattice `ker(N) = {a + b + c = 0}` (B1a/B1b), the exponent-sum bridge and the kernel landing
`identityLandsAugmentationZero` (B1c), the realization family and the round-trip surjection onto the
group ring (B2), the completeness adjudication ledger (B3), and the H2 tie to the shipped `d2` shadow (B4).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingAugmentation
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingSAction
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingNormElement
#assert_no_axioms FX1Poly.Polygraph.Homology.intAddAddComm
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingAugmentationNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingAugmentationAdd
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingAugmentationOfPowerOfT
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingNormElementProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingAugmentationDiagonalProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingSActionProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.normKernelIffAugmentationZero
#assert_no_axioms FX1Poly.Polygraph.Homology.letterExp
#assert_no_axioms FX1Poly.Polygraph.Homology.exponentSumCons
#assert_no_axioms FX1Poly.Polygraph.Homology.exponentSumAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.letterExpInverseSumZero
#assert_no_axioms FX1Poly.Polygraph.Homology.letterExpInverse
#assert_no_axioms FX1Poly.Polygraph.Homology.exponentSumMapInverse
#assert_no_axioms FX1Poly.Polygraph.Homology.exponentSumReverseAux
#assert_no_axioms FX1Poly.Polygraph.Homology.exponentSumReverse
#assert_no_axioms FX1Poly.Polygraph.Homology.exponentSumInvWord
#assert_no_axioms FX1Poly.Polygraph.Homology.exponentSumConsReduced
#assert_no_axioms FX1Poly.Polygraph.Homology.exponentSumReduceInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.intCancelOuter
#assert_no_axioms FX1Poly.Polygraph.Homology.exponentSumConjugation
#assert_no_axioms FX1Poly.Polygraph.Homology.signInt
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugatedRelatorBoundaryExponentIndexZero
#assert_no_axioms FX1Poly.Polygraph.Homology.augmentationOfConjugatedRelatorImage
#assert_no_axioms FX1Poly.Polygraph.Homology.AllRelatorIndexZero
#assert_no_axioms FX1Poly.Polygraph.Homology.exponentSumBoundaryIsThreeAugmentation
#assert_no_axioms FX1Poly.Polygraph.Homology.identityLandsAugmentationZero
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationIdentityAugmentationIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.doublyConjugatedIdentityBoundaryVanishes
#assert_no_axioms FX1Poly.Polygraph.Homology.doublyConjugatedIdentityAugmentationIsZero

end FX1PolyAudit
