import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreeSignedGroupDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingBraid.BraidThreeSignedGroupDecision — zero-axiom gate (the full `B_3` GROUP word-problem decision)

Per-declaration zero-axiom gate for the signed braid-group brick 3, the full braid-GROUP word problem
decided: SOUNDNESS (positive/`Δ⁻¹`/negative dominoes, the transducer domino, the reconstruction, the
round-trip), COMPLETENESS (the signed braid-agreement through the commutation, the signed `Δ`-factorization
in both orders, the congruence), the total decider + instance, the positive-word embedding with its canon
theorem and both transfer directions, THE EMBEDDING AGREEMENT with the shipped positive decider, the canon
value smokes, the decide fires (seven accepting, four rejecting, one embedded cross-check), and the
established marker.

Two independent mechanisms per the AuditAll-semantics rule: the fuel-based `#assert_no_axioms` gate (one per
declaration, throws on any axiom) and a separate `#print axioms` cross-check over the headline declarations.
Each must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.braidSignedPositiveDominoWithPower
#assert_no_axioms FX1Poly.Polygraph.braidSignedDeltaInvDomino
#assert_no_axioms FX1Poly.Polygraph.braidSignedNegativeDomino
#assert_no_axioms FX1Poly.Polygraph.braidSignedPositiveAtomDomino
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependAtom_readback_conv
#assert_no_axioms FX1Poly.Polygraph.braidSignedConv_toReadback
#assert_no_axioms FX1Poly.Polygraph.braidSignedConv_of_normalizeWord_eq
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtom_braidAgreementNonNegative
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtom_braidAgreementNegative
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtom_braidAgreement
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtom_deltaFactorizationNegative
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtom_deltaFactorization
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtom_deltaFactorizationSwapped
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord_congr_of_conv
#assert_no_axioms FX1Poly.Polygraph.decideBraidThreeGroupConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableBraidThreeSignedConv
#assert_no_axioms FX1Poly.Polygraph.braidSignedWordOfPositiveWord
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord_ofPositiveWord_ofLength
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord_ofPositiveWord
#assert_no_axioms FX1Poly.Polygraph.braidThreeConv_ofSignedConvOnPositive
#assert_no_axioms FX1Poly.Polygraph.braidSignedConv_ofPositiveConv
#assert_no_axioms FX1Poly.Polygraph.decideBraidThreeGroupConv_agreesWithPositive
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord_sigmaOneCancelPair
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord_sigmaOneInvCancelPair
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord_deltaInverseSquared
#assert_no_axioms FX1Poly.Polygraph.braidSignedConv_conjugationPair
#assert_no_axioms FX1Poly.Polygraph.braidSignedGroupDecide_true_on_sigmaOneCancel
#assert_no_axioms FX1Poly.Polygraph.braidSignedGroupDecide_true_on_sigmaOneInvCancel
#assert_no_axioms FX1Poly.Polygraph.braidSignedGroupDecide_true_on_deltaTimesInverse
#assert_no_axioms FX1Poly.Polygraph.braidSignedGroupDecide_true_on_deltaInverseTimesDelta
#assert_no_axioms FX1Poly.Polygraph.braidSignedGroupDecide_true_on_conjugation
#assert_no_axioms FX1Poly.Polygraph.braidSignedGroupDecide_true_on_mixedFiveAtom
#assert_no_axioms FX1Poly.Polygraph.braidSignedGroupDecide_true_on_deltaInverseSquared
#assert_no_axioms FX1Poly.Polygraph.braidSignedGroupDecide_false_on_atoms
#assert_no_axioms FX1Poly.Polygraph.braidSignedGroupDecide_false_on_atomVersusInverse
#assert_no_axioms FX1Poly.Polygraph.braidSignedGroupDecide_false_on_wordVersusInverse
#assert_no_axioms FX1Poly.Polygraph.braidSignedGroupDecide_false_on_commutatorFiveAtom
#assert_no_axioms FX1Poly.Polygraph.braidSignedGroupDecide_true_on_embeddedBraidPair
#assert_no_axioms FX1Poly.Polygraph.fxBraid_hasBraidGroupDecided

/-! ## Independent `#print axioms` cross-check — both directions, the decider, and the agreement -/

#print axioms FX1Poly.Polygraph.braidSignedConv_toReadback
#print axioms FX1Poly.Polygraph.braidSignedConv_of_normalizeWord_eq
#print axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtom_braidAgreement
#print axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtom_deltaFactorization
#print axioms FX1Poly.Polygraph.braidSignedNormalizeWord_congr_of_conv
#print axioms FX1Poly.Polygraph.decideBraidThreeGroupConv
#print axioms FX1Poly.Polygraph.instDecidableBraidThreeSignedConv
#print axioms FX1Poly.Polygraph.braidSignedNormalizeWord_ofPositiveWord
#print axioms FX1Poly.Polygraph.decideBraidThreeGroupConv_agreesWithPositive
#print axioms FX1Poly.Polygraph.braidSignedGroupDecide_true_on_deltaInverseSquared
#print axioms FX1Poly.Polygraph.braidSignedGroupDecide_false_on_commutatorFiveAtom
#print axioms FX1Poly.Polygraph.fxBraid_hasBraidGroupDecided

end FX1PolyAudit
