import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.CrossedModuleFreeGroupMeasureInduction

/-! # FX1PolyAudit/Polygraph/Homology/CrossedModuleFreeGroupMeasureInduction — zero-axiom gate (the
    measure induction, the general well-formed residual, and the UNCONDITIONAL instance iso for `⟨s | s³⟩`)

Per-declaration zero-axiom gate for WP-2GROUP r6 (#2199).  Every declaration must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## B1 — the atomic layer (self-shift, inverse congruence, genE-form commute, block float) -/

#assert_no_axioms FX1Poly.Polygraph.Homology.notNotBool
#assert_no_axioms FX1Poly.Polygraph.Homology.invGenInvGen
#assert_no_axioms FX1Poly.Polygraph.Homology.freeCrossedInvGenCongr
#assert_no_axioms FX1Poly.Polygraph.Homology.selfConjugateShiftRaw
#assert_no_axioms FX1Poly.Polygraph.Homology.selfConjugateShiftEq
#assert_no_axioms FX1Poly.Polygraph.Homology.commutePosLeft
#assert_no_axioms FX1Poly.Polygraph.Homology.listAppendNilRight
#assert_no_axioms FX1Poly.Polygraph.Homology.listAppendAssociative
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedInverse
#assert_no_axioms FX1Poly.Polygraph.Homology.crossedInverseAppend
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferConjugateInvGenRight
#assert_no_axioms FX1Poly.Polygraph.Homology.peifferInvListCongr
#assert_no_axioms FX1Poly.Polygraph.Homology.invListCongr
#assert_no_axioms FX1Poly.Polygraph.Homology.commuteBothNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.freeCrossedGenEFormCommute
#assert_no_axioms FX1Poly.Polygraph.Homology.commutePastBlock
#assert_no_axioms FX1Poly.Polygraph.Homology.genEFormCommuteProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.genEFormCommuteBothNegProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.selfConjugateShiftProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.freeCrossedMeasureAtomicLayerIsComplete

/-! ## B2 — the NORMALIZE phase inductions -/

#assert_no_axioms FX1Poly.Polygraph.Homology.genEformOfResidue
#assert_no_axioms FX1Poly.Polygraph.Homology.genEformSigned
#assert_no_axioms FX1Poly.Polygraph.Homology.shiftUpThree
#assert_no_axioms FX1Poly.Polygraph.Homology.shiftDownThree
#assert_no_axioms FX1Poly.Polygraph.Homology.reduceWordSignPowerNeg
#assert_no_axioms FX1Poly.Polygraph.Homology.freeCrossedSignPowerNegStrip
#assert_no_axioms FX1Poly.Polygraph.Homology.normalizePosPower
#assert_no_axioms FX1Poly.Polygraph.Homology.normalizeNegPower
#assert_no_axioms FX1Poly.Polygraph.Homology.normalizeSignPowerInt
#assert_no_axioms FX1Poly.Polygraph.Homology.normalizeGenTrue
#assert_no_axioms FX1Poly.Polygraph.Homology.normalizeGen
#assert_no_axioms FX1Poly.Polygraph.Homology.normalizeGenProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.normalizeNegPowerProbe
#assert_no_axioms FX1Poly.Polygraph.Homology.freeCrossedMeasureNormalizeIsComplete

end FX1PolyAudit
