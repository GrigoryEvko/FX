import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.CrossedModuleCyclicPowerInvariant

/-! # FX1PolyAudit/Polygraph/Homology/CrossedModuleCyclicPowerInvariant — zero-axiom gate (the general
    `ZZ[ZZ/n]` separating invariant on the free crossed module of `⟨s | sⁿ⟩`, its exponent-`n`
    Peiffer-invariance, and the mechanized `π₂⟨s | sⁿ⟩ ≠ 0` for every `n ≥ 2`)

Per-declaration zero-axiom gate for WP-2GROUP r8 (#2199): the list cyclic-rotation carrier and its
mutual-inverse/length/cyclicity laws (V1), the invariant map `crossedModuleImageN : E → ZZ[ZZ/n]` with its
length invariant and append-homomorphism (V2), the exponent-`n` Peiffer relation `PeifferEquivAt` with the
`boundaryAtFixesLength` crux and the keystone `crossedModuleImageRespectsPeifferAt` (V3), and the
separation `rotationNotPeifferTrivialN` (`π₂⟨s | sⁿ⟩ ≠ 0` ∀ `n ≥ 2`) with the `n = 1` degenerate control
(V4).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  The polymorphic-recursion propext trap is dodged by MONOMORPHIC list helpers
(`List Int` / `List SignedLetter`). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.intListAppendNil
#assert_no_axioms FX1Poly.Polygraph.Homology.intListAppendAssoc
#assert_no_axioms FX1Poly.Polygraph.Homology.intListLengthAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.letterListAppendAssoc
#assert_no_axioms FX1Poly.Polygraph.Homology.reverseAuxAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.reverseConsLaw
#assert_no_axioms FX1Poly.Polygraph.Homology.rotateForward
#assert_no_axioms FX1Poly.Polygraph.Homology.lastElemD
#assert_no_axioms FX1Poly.Polygraph.Homology.initSegment
#assert_no_axioms FX1Poly.Polygraph.Homology.rotateBackward
#assert_no_axioms FX1Poly.Polygraph.Homology.zeroVec
#assert_no_axioms FX1Poly.Polygraph.Homology.basisE0
#assert_no_axioms FX1Poly.Polygraph.Homology.vecAdd
#assert_no_axioms FX1Poly.Polygraph.Homology.vecNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.signScaleN
#assert_no_axioms FX1Poly.Polygraph.Homology.headCoeff
#assert_no_axioms FX1Poly.Polygraph.Homology.coeffSum
#assert_no_axioms FX1Poly.Polygraph.Homology.rotateForwardProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.rotateBackwardProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.basisE0Probe
#assert_no_axioms FX1Poly.Polygraph.Homology.vecAddProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.zeroVecLength
#assert_no_axioms FX1Poly.Polygraph.Homology.basisE0Length
#assert_no_axioms FX1Poly.Polygraph.Homology.rotateForwardLength
#assert_no_axioms FX1Poly.Polygraph.Homology.initSegmentLength
#assert_no_axioms FX1Poly.Polygraph.Homology.rotateBackwardLength
#assert_no_axioms FX1Poly.Polygraph.Homology.lastElemDAppendSingle
#assert_no_axioms FX1Poly.Polygraph.Homology.initSegmentAppendSingle
#assert_no_axioms FX1Poly.Polygraph.Homology.initAppendLast
#assert_no_axioms FX1Poly.Polygraph.Homology.rotateBackwardSnoc
#assert_no_axioms FX1Poly.Polygraph.Homology.rotateBackwardForward
#assert_no_axioms FX1Poly.Polygraph.Homology.rotateForwardBackward
#assert_no_axioms FX1Poly.Polygraph.Homology.letterRotate
#assert_no_axioms FX1Poly.Polygraph.Homology.applyWordRotate
#assert_no_axioms FX1Poly.Polygraph.Homology.letterRotateLength
#assert_no_axioms FX1Poly.Polygraph.Homology.applyWordRotateLength
#assert_no_axioms FX1Poly.Polygraph.Homology.applyWordRotateAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.letterRotateInverseCancel
#assert_no_axioms FX1Poly.Polygraph.Homology.letterRotateInverseSelf
#assert_no_axioms FX1Poly.Polygraph.Homology.applyWordRotateConsReduced
#assert_no_axioms FX1Poly.Polygraph.Homology.applyWordRotateReduceInvariant
#assert_no_axioms FX1Poly.Polygraph.Homology.invWordCons
#assert_no_axioms FX1Poly.Polygraph.Homology.applyWordRotateInverseCancel
#assert_no_axioms FX1Poly.Polygraph.Homology.rotateForwardPow
#assert_no_axioms FX1Poly.Polygraph.Homology.rotateForwardPowCommute
#assert_no_axioms FX1Poly.Polygraph.Homology.applyWordRotateSignPowerPos
#assert_no_axioms FX1Poly.Polygraph.Homology.rotateForwardPowFrontAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.rotateForwardPowFixesLength
#assert_no_axioms FX1Poly.Polygraph.Homology.signPowerPosFixesLength
#assert_no_axioms FX1Poly.Polygraph.Homology.invSignPowerPosFixesLength
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugatorVecN
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugatedRelatorImageN
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleImageN
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugatorVecNLength
#assert_no_axioms FX1Poly.Polygraph.Homology.vecNegLength
#assert_no_axioms FX1Poly.Polygraph.Homology.signScaleNLength
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugatedRelatorImageNLength
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationImageThreeProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationImageFourProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.emptyImageNProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.vecAddAssoc
#assert_no_axioms FX1Poly.Polygraph.Homology.vecAddCongr
#assert_no_axioms FX1Poly.Polygraph.Homology.vecAddZeroVecLeftSelf
#assert_no_axioms FX1Poly.Polygraph.Homology.vecAddZeroVecRightSelf
#assert_no_axioms FX1Poly.Polygraph.Homology.vecAddLengthEq
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleImageNLength
#assert_no_axioms FX1Poly.Polygraph.Homology.vecAddZeroVecLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.vecAddZeroVecRight
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleImageNAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferConjugateAt
#assert_no_axioms FX1Poly.Polygraph.Homology.PeifferEquivAt
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugatedRelatorImageNInvGen
#assert_no_axioms FX1Poly.Polygraph.Homology.boundaryAtFixesLength
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferConjugatorVecEq
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferMoveImageN
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleImageRespectsPeifferAt
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationImageHeadCoeffAtLeastTwo
#assert_no_axioms FX1Poly.Polygraph.Homology.emptyImageHeadCoeff
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationImageSeparatesN
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationNotPeifferTrivialN
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationImageDegenerateAtOne
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationImageAugmentationVanishesThree
#assert_no_axioms FX1Poly.Polygraph.Homology.CyclicPowerInvariantLedger
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicPowerInvariantLedger
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleCyclicPowerInvariantIsComplete

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
`#assert_no_axioms`; the core `#print axioms` command does not truncate). -/

#print axioms FX1Poly.Polygraph.Homology.rotateForwardPowFixesLength
#print axioms FX1Poly.Polygraph.Homology.boundaryAtFixesLength
#print axioms FX1Poly.Polygraph.Homology.crossedModuleImageRespectsPeifferAt
#print axioms FX1Poly.Polygraph.Homology.rotationImageSeparatesN
#print axioms FX1Poly.Polygraph.Homology.rotationNotPeifferTrivialN

end FX1PolyAudit
