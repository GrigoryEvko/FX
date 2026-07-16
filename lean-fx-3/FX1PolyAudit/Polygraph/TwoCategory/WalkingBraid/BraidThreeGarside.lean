import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreeGarside

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingBraid.BraidThreeGarside — zero-axiom gate (the Garside Δ-layer + simple-stratum decision)

Per-declaration zero-axiom gate for the Garside half of the walking positive braid `B_3^+`: the whiskering
congruence engine (`convWhiskerRight`, `convWhiskerLeftOfLength`, `convWhiskerLeft`, `convComposeCongr`), the
Garside element Δ + its second representation, the two two-letter simple words, the Δ-conjugations, the
centrality of Δ² (through the whiskering engine), the simple-divisor lattice, the simple stratum in bijection
with `S_3` (the injective `simplePerm` via the retraction `simpleOfPerm`), the total simple-stratum decider and
its non-vacuity witnesses, and the markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.convWhiskerRight
#assert_no_axioms FX1Poly.Polygraph.convWhiskerLeftOfLength
#assert_no_axioms FX1Poly.Polygraph.convWhiskerLeft
#assert_no_axioms FX1Poly.Polygraph.convComposeCongr
#assert_no_axioms FX1Poly.Polygraph.braidThreeDelta
#assert_no_axioms FX1Poly.Polygraph.braidThreeDelta_length
#assert_no_axioms FX1Poly.Polygraph.braidThreeDelta_rightRepresentation
#assert_no_axioms FX1Poly.Polygraph.braidThreeSigma1Sigma2
#assert_no_axioms FX1Poly.Polygraph.braidThreeSigma2Sigma1
#assert_no_axioms FX1Poly.Polygraph.braidThreeDeltaConjugateSigma1
#assert_no_axioms FX1Poly.Polygraph.braidThreeDeltaConjugateSigma2
#assert_no_axioms FX1Poly.Polygraph.braidThreeDeltaSquared
#assert_no_axioms FX1Poly.Polygraph.braidThreeDeltaSquared_length
#assert_no_axioms FX1Poly.Polygraph.braidThreeDeltaSquaredCentralSigma1
#assert_no_axioms FX1Poly.Polygraph.braidThreeDeltaSquaredCentralSigma2
#assert_no_axioms FX1Poly.Polygraph.braidThreeDelta_leftDivisibleBy_identity
#assert_no_axioms FX1Poly.Polygraph.braidThreeDelta_leftDivisibleBy_sigmaOne
#assert_no_axioms FX1Poly.Polygraph.braidThreeDelta_leftDivisibleBy_sigmaTwo
#assert_no_axioms FX1Poly.Polygraph.braidThreeDelta_leftDivisibleBy_sigmaOneTwo
#assert_no_axioms FX1Poly.Polygraph.braidThreeDelta_leftDivisibleBy_sigmaTwoOne
#assert_no_axioms FX1Poly.Polygraph.braidThreeDelta_leftDivisibleBy_delta
#assert_no_axioms FX1Poly.Polygraph.braidThreeDelta_rightDivisibleBy_sigmaOne
#assert_no_axioms FX1Poly.Polygraph.braidThreeDelta_rightDivisibleBy_sigmaTwo
#assert_no_axioms FX1Poly.Polygraph.SimpleThree
#assert_no_axioms FX1Poly.Polygraph.simpleWord
#assert_no_axioms FX1Poly.Polygraph.simplePerm
#assert_no_axioms FX1Poly.Polygraph.simplePerm_simpleIdentity
#assert_no_axioms FX1Poly.Polygraph.simplePerm_simpleSigmaOne
#assert_no_axioms FX1Poly.Polygraph.simplePerm_simpleSigmaTwo
#assert_no_axioms FX1Poly.Polygraph.simplePerm_simpleSigmaOneTwo
#assert_no_axioms FX1Poly.Polygraph.simplePerm_simpleSigmaTwoOne
#assert_no_axioms FX1Poly.Polygraph.simplePerm_simpleDelta
#assert_no_axioms FX1Poly.Polygraph.simpleOfPerm
#assert_no_axioms FX1Poly.Polygraph.simpleOfPerm_simplePerm
#assert_no_axioms FX1Poly.Polygraph.simplePerm_injective
#assert_no_axioms FX1Poly.Polygraph.braidThreeSimpleConv_of_eq
#assert_no_axioms FX1Poly.Polygraph.decideBraidThreeSimpleConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableBraidThreeSimpleConv
#assert_no_axioms FX1Poly.Polygraph.braidThreeSimpleDecide_true_on_delta
#assert_no_axioms FX1Poly.Polygraph.braidThreeSimpleDecide_false_on_atoms
#assert_no_axioms FX1Poly.Polygraph.braidThreeSimpleDecide_false_on_twoLetters
#assert_no_axioms FX1Poly.Polygraph.fxBraid_hasGarsideDeltaLayer
#assert_no_axioms FX1Poly.Polygraph.fxBraid_hasSimpleStratumConvDecided
#assert_no_axioms FX1Poly.Polygraph.fxBraid_hasFullWordProblemDecided

end FX1PolyAudit
