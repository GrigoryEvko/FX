import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.CrossedModuleIdentityInvariant

/-! # FX1PolyAudit/Polygraph/Homology/CrossedModuleIdentityInvariant — zero-axiom gate (the
    `ZZ[ZZ/3] ≅ ZZ³` separating invariant on the free crossed module of `⟨s | s³⟩`, its Peiffer-
    invariance, and the first machine-checked nontrivial identity among relations)

Per-declaration zero-axiom gate for WP-2GROUP r2 (#2199): the group-ring carrier and its abelian laws
(B1), the residue "image of `w` in `G`" and the invariant map `crossedModuleImage : E → ZZ[ZZ/3]` with
its append-homomorphism and the separating value `image ζ = (−1, 1, 0)` (B2), the `ZZ/3` Cayley table
and shift-distribution laws through the residue homomorphism (`reduceResiduePreserved`,
`wordResidueInvWord`, `boundaryResidueIsZero`), the Peiffer-invariance keystone
`crossedModuleImageRespectsPeiffer` (B3), the non-triviality theorem
`rotationIdentityNotPeifferTrivial` (`¬ PeifferEquiv ζ []`, `π₂ ≠ 0` element-level), and the closed
ledger node (B4/B5).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.GroupRingZmod3
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingZero
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingAdd
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingEq
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingAddZero
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingZeroAdd
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingAddAssoc
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingNegNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.intCancelMiddle
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingCancelMiddle
#assert_no_axioms FX1Poly.Polygraph.Homology.ZmodThree
#assert_no_axioms FX1Poly.Polygraph.Homology.powerOfT
#assert_no_axioms FX1Poly.Polygraph.Homology.signScale
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingAddProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingNegProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.powerOfTProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingCancelProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.signScaleNegProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.shiftUp
#assert_no_axioms FX1Poly.Polygraph.Homology.shiftDown
#assert_no_axioms FX1Poly.Polygraph.Homology.letterShift
#assert_no_axioms FX1Poly.Polygraph.Homology.wordResidue
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugatedRelatorImage
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleImage
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleImageAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationIdentityImageIsSeparating
#assert_no_axioms FX1Poly.Polygraph.Homology.emptyImageIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferProbeImageCoherent
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferProbeImageValue
#assert_no_axioms FX1Poly.Polygraph.Homology.addZmod3
#assert_no_axioms FX1Poly.Polygraph.Homology.negZmod3
#assert_no_axioms FX1Poly.Polygraph.Homology.addZmod3ZeroLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.addZmod3ZeroRight
#assert_no_axioms FX1Poly.Polygraph.Homology.addZmod3RightNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.shiftUpShiftDown
#assert_no_axioms FX1Poly.Polygraph.Homology.shiftDownShiftUp
#assert_no_axioms FX1Poly.Polygraph.Homology.shiftUpAddZmod3
#assert_no_axioms FX1Poly.Polygraph.Homology.shiftDownAddZmod3
#assert_no_axioms FX1Poly.Polygraph.Homology.letterShiftAddZmod3
#assert_no_axioms FX1Poly.Polygraph.Homology.shiftUpAddZmod3Right
#assert_no_axioms FX1Poly.Polygraph.Homology.shiftDownAddZmod3Right
#assert_no_axioms FX1Poly.Polygraph.Homology.letterShiftAddZmod3Right
#assert_no_axioms FX1Poly.Polygraph.Homology.shiftDownNegIsNegShiftUp
#assert_no_axioms FX1Poly.Polygraph.Homology.shiftUpNegIsNegShiftDown
#assert_no_axioms FX1Poly.Polygraph.Homology.letterShiftInverseNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.applyWordShift
#assert_no_axioms FX1Poly.Polygraph.Homology.wordResidueAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.applyWordShiftIsAdd
#assert_no_axioms FX1Poly.Polygraph.Homology.wordResidueAppendAdd
#assert_no_axioms FX1Poly.Polygraph.Homology.letterShiftInverseCancel
#assert_no_axioms FX1Poly.Polygraph.Homology.consReducedResidue
#assert_no_axioms FX1Poly.Polygraph.Homology.reduceResiduePreserved
#assert_no_axioms FX1Poly.Polygraph.Homology.wordResidueMapInverse
#assert_no_axioms FX1Poly.Polygraph.Homology.wordResidueReverseAux
#assert_no_axioms FX1Poly.Polygraph.Homology.wordResidueReverse
#assert_no_axioms FX1Poly.Polygraph.Homology.wordResidueInvWord
#assert_no_axioms FX1Poly.Polygraph.Homology.relatorResidueIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.invRelatorResidueIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugationResidueZero
#assert_no_axioms FX1Poly.Polygraph.Homology.boundaryResidueIsZero
#assert_no_axioms FX1Poly.Polygraph.Homology.signScaleNotIsNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.conjugatedRelatorImageInvGen
#assert_no_axioms FX1Poly.Polygraph.Homology.groupRingAddCongr
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferMoveImage
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleImageRespectsPeiffer
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationIdentityImageNeqEmptyImage
#assert_no_axioms FX1Poly.Polygraph.Homology.rotationIdentityNotPeifferTrivial
#assert_no_axioms FX1Poly.Polygraph.Homology.cyclicThreeSeparatingInvariantLedger
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedModuleIdentityInvariantIsComplete

end FX1PolyAudit
