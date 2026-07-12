import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.CrossedModuleTorusAsphericity

/-! # FX1PolyAudit/Polygraph/Homology/CrossedModuleTorusAsphericity — zero-axiom gate (the `ZZ[ZZ^2]`
    relation-module invariant on the free crossed module of `⟨a, b | [a, b]⟩`, its Peiffer-invariance, and
    the machine-checked kernel-vanishing witnesses + Fox-Jacobian record)

Per-declaration zero-axiom gate for WP-2GROUP r9 (#2199): the `ZZ^2`-abelianization carrier `abWordTorus`
and its `expGenTorus` reduce/append/inverse laws (V1), the invariant `torusImageCoeffAt : E → ZZ[ZZ^2]`
with its append-homomorphism and the torus boundary `commutatorConjugatedBoundary` whose abelianization
vanishes (V2), the torus Peiffer relation `PeifferEquivTorus` with the keystone `torusImageRespectsPeiffer`
(V3), and the kernel-vanishing witnesses + ζ-mirror contrast + Fox-Jacobian record (V4).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  The polymorphic-recursion propext trap is dodged by MONOMORPHIC `List SignedLetter` / `Int` /
`Int × Int` helpers; `signInt` is REUSED (not redefined); generator equality is the OWN structural
`torusNatEqOfBeqTrue` (never Init's `Nat.eq_of_beq_eq_true`). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.torusNatEqOfBeqTrue
#assert_no_axioms FX1Poly.Polygraph.Homology.torusProdMkEq
#assert_no_axioms FX1Poly.Polygraph.Homology.torusIntAddCongr
#assert_no_axioms FX1Poly.Polygraph.Homology.torusIntCancelMiddle
#assert_no_axioms FX1Poly.Polygraph.Homology.torusMatchedInt
#assert_no_axioms FX1Poly.Polygraph.Homology.torusMatchedIntCancelPair
#assert_no_axioms FX1Poly.Polygraph.Homology.torusMatchedIntCancelPairRev
#assert_no_axioms FX1Poly.Polygraph.Homology.torusMatchedIntNegPos
#assert_no_axioms FX1Poly.Polygraph.Homology.torusMatchedIntNegNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.expGenLetter
#assert_no_axioms FX1Poly.Polygraph.Homology.expGenTorus
#assert_no_axioms FX1Poly.Polygraph.Homology.expGenLetterInverse
#assert_no_axioms FX1Poly.Polygraph.Homology.expGenLetterInverseCancel
#assert_no_axioms FX1Poly.Polygraph.Homology.expGenTorusConsReduced
#assert_no_axioms FX1Poly.Polygraph.Homology.expGenTorusReduceInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.expGenTorusAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.expGenTorusInvWord
#assert_no_axioms FX1Poly.Polygraph.Homology.abWordTorus
#assert_no_axioms FX1Poly.Polygraph.Homology.torusPairAdd
#assert_no_axioms FX1Poly.Polygraph.Homology.torusPairNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.torusPairAddZeroLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.torusPairAddZeroRight
#assert_no_axioms FX1Poly.Polygraph.Homology.torusPairAddNegCancel
#assert_no_axioms FX1Poly.Polygraph.Homology.abWordTorusReduceInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.abWordTorusAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.abWordTorusInvWord
#assert_no_axioms FX1Poly.Polygraph.Homology.abWordTorusCommutatorRelator
#assert_no_axioms FX1Poly.Polygraph.Homology.abWordTorusInvCommutatorRelator
#assert_no_axioms FX1Poly.Polygraph.Homology.commutatorConjugatedBoundary
#assert_no_axioms FX1Poly.Polygraph.Homology.torusPartialBoundary
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugatedBodyAbelianizesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.commutatorConjugatedBoundaryAbelianizesToZero
#assert_no_axioms FX1Poly.Polygraph.Homology.intBeqTorus
#assert_no_axioms FX1Poly.Polygraph.Homology.torusPairBeq
#assert_no_axioms FX1Poly.Polygraph.Homology.torusSignContribGuarded
#assert_no_axioms FX1Poly.Polygraph.Homology.torusCoeffContribution
#assert_no_axioms FX1Poly.Polygraph.Homology.torusImageCoeffAt
#assert_no_axioms FX1Poly.Polygraph.Homology.torusImageCoeffAtAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.torusSignIntNotIsNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.torusSignContribGuardedNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.torusCoeffContributionInvGen
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferConjugateTorus
#assert_no_axioms FX1Poly.Polygraph.Homology.PeifferEquivTorus
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferConjugateTorusAbEq
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferConjugateTorusCoeffEq
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferMoveImageTorus
#assert_no_axioms FX1Poly.Polygraph.Homology.torusImageRespectsPeiffer
#assert_no_axioms FX1Poly.Polygraph.Homology.torusKernelWitnessOne
#assert_no_axioms FX1Poly.Polygraph.Homology.torusKernelWitnessOneInKernel
#assert_no_axioms FX1Poly.Polygraph.Homology.torusKernelWitnessOneImageVanishesAtA
#assert_no_axioms FX1Poly.Polygraph.Homology.torusKernelWitnessOneImageVanishesAtUnit
#assert_no_axioms FX1Poly.Polygraph.Homology.torusContrastWitnessTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.torusContrastWitnessTwoImageAtA
#assert_no_axioms FX1Poly.Polygraph.Homology.torusContrastWitnessTwoImageAtUnit
#assert_no_axioms FX1Poly.Polygraph.Homology.torusContrastWitnessTwoNotInKernel
#assert_no_axioms FX1Poly.Polygraph.Homology.torusKernelWitnessThree
#assert_no_axioms FX1Poly.Polygraph.Homology.torusKernelWitnessThreeInKernel
#assert_no_axioms FX1Poly.Polygraph.Homology.torusKernelWitnessThreeImageVanishesAtUnit
#assert_no_axioms FX1Poly.Polygraph.Homology.torusKernelWitnessFour
#assert_no_axioms FX1Poly.Polygraph.Homology.torusKernelWitnessFourInKernel
#assert_no_axioms FX1Poly.Polygraph.Homology.torusKernelWitnessFourImageVanishesAtA
#assert_no_axioms FX1Poly.Polygraph.Homology.torusKernelWitnessFourImageVanishesAtB
#assert_no_axioms FX1Poly.Polygraph.Homology.foxDerivACoeff
#assert_no_axioms FX1Poly.Polygraph.Homology.foxDerivBCoeff
#assert_no_axioms FX1Poly.Polygraph.Homology.foxDerivACoeffAtUnit
#assert_no_axioms FX1Poly.Polygraph.Homology.foxDerivACoeffAtB
#assert_no_axioms FX1Poly.Polygraph.Homology.foxDerivBCoeffAtA
#assert_no_axioms FX1Poly.Polygraph.Homology.foxDerivBCoeffAtUnit
#assert_no_axioms FX1Poly.Polygraph.Homology.CrossedModuleTorusAsphericityLedger
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleTorusAsphericityLedger
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleTorusAsphericityIsComplete

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
`#assert_no_axioms`; the core `#print axioms` command does not truncate). -/

#print axioms FX1Poly.Polygraph.Homology.expGenTorusReduceInvariant
#print axioms FX1Poly.Polygraph.Homology.commutatorConjugatedBoundaryAbelianizesToZero
#print axioms FX1Poly.Polygraph.Homology.peifferMoveImageTorus
#print axioms FX1Poly.Polygraph.Homology.torusImageRespectsPeiffer
#print axioms FX1Poly.Polygraph.Homology.torusKernelWitnessOneInKernel
#print axioms FX1Poly.Polygraph.Homology.torusContrastWitnessTwoImageAtA
#print axioms FX1Poly.Polygraph.Homology.torusContrastWitnessTwoNotInKernel

end FX1PolyAudit
