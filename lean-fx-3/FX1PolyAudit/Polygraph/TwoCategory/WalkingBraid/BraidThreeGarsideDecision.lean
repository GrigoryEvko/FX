import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreeGarsideDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingBraid.BraidThreeGarsideDecision — zero-axiom gate (the FULL `B_3^+` word-problem decision)

Per-declaration zero-axiom gate for WP-BRAID-3, the full positive-braid-monoid word problem decided via the
left-greedy Garside normal form: the atom/proper-simple/canon carriers and their manual `decEq`s, the carrying
transducer (`braidPrependAtomToFactors` / `braidPrependAtomWithPower` / `braidPrependAtom` and its
definitional-reduction smoke), the mode-generic normalizer and its defining equations, the cons-based readback,
SOUNDNESS (the domino step `braidPrependAtom_readback_conv`, the length-generalized reconstruction, the
round-trip `braidThreeConv_of_normalizeWord_eq`), the left-greedy invariant (`braidHandoffAllows` /
`braidIsLeftGreedy` / the two preservation lemmas / `braidNormalizeWord_greedy`), COMPLETENESS (the
braid-agreement crux `braidPrependAtom_braidAgreement` + `braidNormalizeWord_congr_of_conv`), the total decider
+ instance, the smoke words, the canon value smokes, the decide smokes, the simple-stratum cross-checks, and
the established marker.

Two independent mechanisms per the AuditAll-semantics rule: the fuel-based `#assert_no_axioms` gate (one per
declaration, throws on any axiom) and a separate `#print axioms` cross-check over the headline declarations.
Each must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.BraidAtom
#assert_no_axioms FX1Poly.Polygraph.braidFlipAtom
#assert_no_axioms FX1Poly.Polygraph.braidAtomOfGenerator
#assert_no_axioms FX1Poly.Polygraph.braidConsAtom
#assert_no_axioms FX1Poly.Polygraph.BraidProperSimple
#assert_no_axioms FX1Poly.Polygraph.braidProperSimpleDecEq
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqBraidProperSimple
#assert_no_axioms FX1Poly.Polygraph.braidProperFactorsDecEq
#assert_no_axioms FX1Poly.Polygraph.BraidGarsideCanon
#assert_no_axioms FX1Poly.Polygraph.braidSuccDelta
#assert_no_axioms FX1Poly.Polygraph.braidGarsideCanonDecEq
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqBraidGarsideCanon
#assert_no_axioms FX1Poly.Polygraph.braidPrependAtomToFactors
#assert_no_axioms FX1Poly.Polygraph.braidPrependAtomWithPower
#assert_no_axioms FX1Poly.Polygraph.braidPrependAtom
#assert_no_axioms FX1Poly.Polygraph.braidPrependAtom_succDelta
#assert_no_axioms FX1Poly.Polygraph.braidNormalizeWord
#assert_no_axioms FX1Poly.Polygraph.braidNormalizeWord_nil
#assert_no_axioms FX1Poly.Polygraph.braidNormalizeWord_cons
#assert_no_axioms FX1Poly.Polygraph.braidProperFactorWord
#assert_no_axioms FX1Poly.Polygraph.braidReadbackFactors
#assert_no_axioms FX1Poly.Polygraph.braidDeltaPowPath
#assert_no_axioms FX1Poly.Polygraph.braidReadbackCanon
#assert_no_axioms FX1Poly.Polygraph.braidReadbackCanon_deltaOne
#assert_no_axioms FX1Poly.Polygraph.braidPrependAtom_readback_conv
#assert_no_axioms FX1Poly.Polygraph.braidConv_toReadback_ofLength
#assert_no_axioms FX1Poly.Polygraph.braidConv_toReadback
#assert_no_axioms FX1Poly.Polygraph.braidThreeConv_of_normalizeWord_eq
#assert_no_axioms FX1Poly.Polygraph.braidHandoffAllows
#assert_no_axioms FX1Poly.Polygraph.braidIsLeftGreedy
#assert_no_axioms FX1Poly.Polygraph.braidPrependAtomToFactors_preservesGreedy
#assert_no_axioms FX1Poly.Polygraph.braidPrependAtomWithPower_preservesGreedy
#assert_no_axioms FX1Poly.Polygraph.braidNormalizeWord_greedy_ofLength
#assert_no_axioms FX1Poly.Polygraph.braidNormalizeWord_greedy
#assert_no_axioms FX1Poly.Polygraph.braidPrependAtom_braidAgreement
#assert_no_axioms FX1Poly.Polygraph.braidNormalizeWord_congr_of_conv
#assert_no_axioms FX1Poly.Polygraph.decideBraidThreeConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableBraidThreeConv
#assert_no_axioms FX1Poly.Polygraph.braidThreeSigma1Sigma1
#assert_no_axioms FX1Poly.Polygraph.braidThreeCarriedLeft
#assert_no_axioms FX1Poly.Polygraph.braidThreeCarriedRight
#assert_no_axioms FX1Poly.Polygraph.braidThreeSigmaOneTwoCubed
#assert_no_axioms FX1Poly.Polygraph.braidNormalizeWord_braidLeft
#assert_no_axioms FX1Poly.Polygraph.braidNormalizeWord_braidRight
#assert_no_axioms FX1Poly.Polygraph.braidNormalizeWord_carriedLeft
#assert_no_axioms FX1Poly.Polygraph.braidNormalizeWord_carriedRight
#assert_no_axioms FX1Poly.Polygraph.braidNormalizeWord_sigmaOneTwoCubed
#assert_no_axioms FX1Poly.Polygraph.braidNormalizeWord_deltaSquared
#assert_no_axioms FX1Poly.Polygraph.braidThreeConv_carriedPair
#assert_no_axioms FX1Poly.Polygraph.braidThreeGarsideDecide_true_on_braidPair
#assert_no_axioms FX1Poly.Polygraph.braidThreeGarsideDecide_true_on_carriedPair
#assert_no_axioms FX1Poly.Polygraph.braidThreeGarsideDecide_true_on_doubleCarry
#assert_no_axioms FX1Poly.Polygraph.braidThreeGarsideDecide_false_on_atoms
#assert_no_axioms FX1Poly.Polygraph.braidThreeGarsideDecide_false_on_twoLetters
#assert_no_axioms FX1Poly.Polygraph.braidThreeGarsideDecide_false_on_lengthSeparated
#assert_no_axioms FX1Poly.Polygraph.braidThreeGarsideDecide_false_on_sigmaSquaredNil
#assert_no_axioms FX1Poly.Polygraph.braidThreeGarsideDecide_agreesWithSimpleStratum_twoLetters
#assert_no_axioms FX1Poly.Polygraph.braidThreeGarsideDecide_agreesWithSimpleStratum_delta
#assert_no_axioms FX1Poly.Polygraph.fxBraid_hasGarsideNormalFormDecision

/-! ## Independent `#print axioms` cross-check — the normalizer, both directions, and the decider -/

#print axioms FX1Poly.Polygraph.braidNormalizeWord
#print axioms FX1Poly.Polygraph.braidPrependAtom_readback_conv
#print axioms FX1Poly.Polygraph.braidConv_toReadback
#print axioms FX1Poly.Polygraph.braidThreeConv_of_normalizeWord_eq
#print axioms FX1Poly.Polygraph.braidPrependAtom_braidAgreement
#print axioms FX1Poly.Polygraph.braidNormalizeWord_greedy
#print axioms FX1Poly.Polygraph.braidNormalizeWord_congr_of_conv
#print axioms FX1Poly.Polygraph.decideBraidThreeConv
#print axioms FX1Poly.Polygraph.instDecidableBraidThreeConv
#print axioms FX1Poly.Polygraph.braidThreeGarsideDecide_true_on_braidPair
#print axioms FX1Poly.Polygraph.braidThreeGarsideDecide_true_on_carriedPair
#print axioms FX1Poly.Polygraph.braidThreeGarsideDecide_true_on_doubleCarry
#print axioms FX1Poly.Polygraph.braidThreeGarsideDecide_false_on_atoms
#print axioms FX1Poly.Polygraph.braidThreeGarsideDecide_false_on_twoLetters
#print axioms FX1Poly.Polygraph.braidThreeGarsideDecide_false_on_lengthSeparated
#print axioms FX1Poly.Polygraph.braidThreeGarsideDecide_false_on_sigmaSquaredNil
#print axioms FX1Poly.Polygraph.fxBraid_hasGarsideNormalFormDecision

end FX1PolyAudit
