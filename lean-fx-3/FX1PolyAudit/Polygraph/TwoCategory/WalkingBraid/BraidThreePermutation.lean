import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreePermutation

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingBraid.BraidThreePermutation — zero-axiom gate (the `S_3` permutation model + SOUNDNESS)

Per-declaration zero-axiom gate for the walking braid `B_3^+` underlying-permutation model: the strand-slot
type + its manual `DecidableEq`, the one-line `S_3` permutation structure + its componentwise manual
`DecidableEq`, the crossing action `applyGen`, the underlying-permutation fold `braidThreePermutationOf` and its
defining / word smokes, the braid-relation `S_3` witness, the SOUNDNESS theorem, the non-vacuity witnesses, the
non-injectivity (honesty-boundary) witness, and the markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ThreeIdx
#assert_no_axioms FX1Poly.Polygraph.threeIdxDecEq
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqThreeIdx
#assert_no_axioms FX1Poly.Polygraph.SymThree
#assert_no_axioms FX1Poly.Polygraph.symThreeIdentity
#assert_no_axioms FX1Poly.Polygraph.symThreeDecEq
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqSymThree
#assert_no_axioms FX1Poly.Polygraph.applyGen
#assert_no_axioms FX1Poly.Polygraph.braidThreePermutationOf
#assert_no_axioms FX1Poly.Polygraph.braidThreePermutationOf_nil
#assert_no_axioms FX1Poly.Polygraph.braidThreePermutationOf_consSigma1
#assert_no_axioms FX1Poly.Polygraph.braidThreePermutationOf_consSigma2
#assert_no_axioms FX1Poly.Polygraph.braidThreePermutationOf_cons
#assert_no_axioms FX1Poly.Polygraph.braidThreePermutationOf_braidLeft
#assert_no_axioms FX1Poly.Polygraph.braidThreePermutationOf_braidRight
#assert_no_axioms FX1Poly.Polygraph.braidThreeApplyGenBraidRelation
#assert_no_axioms FX1Poly.Polygraph.braidThreePermutationOf_congr_of_conv
#assert_no_axioms FX1Poly.Polygraph.braidThreeConv_braidLeft_braidRight
#assert_no_axioms FX1Poly.Polygraph.braidThreeNotConv_sigma1_sigma2
#assert_no_axioms FX1Poly.Polygraph.braidThreeNotConv_sigma1_nil
#assert_no_axioms FX1Poly.Polygraph.braidThreePermutationOf_sigma1Sigma1_eq_nil
#assert_no_axioms FX1Poly.Polygraph.fxBraidThree_hasPermutationSoundness
#assert_no_axioms FX1Poly.Polygraph.fxBraid_hasSignatureAndPermutationSoundness
#assert_no_axioms FX1Poly.Polygraph.fxBraidThree_hasWordProblemDecided

end FX1PolyAudit
