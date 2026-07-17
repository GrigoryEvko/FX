import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreeSignedWord

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingBraid.BraidThreeSignedWord — zero-axiom gate (the signed `B_3` alphabet + relation)

Per-declaration zero-axiom gate for the signed braid-group brick 1: the four-atom signed alphabet, the
`Δ`/`Δ⁻¹` words, the signed convertibility (braid relation + four cancellations + congruence closure), the
derived toolkit (the `Δ`-cancellation chains, the DERIVED inverse braid relation, the `Δ⁻¹`-conjugation
flips, the left-complement expansions), the non-vacuity smokes, and the established marker.

Two independent mechanisms per the AuditAll-semantics rule: the fuel-based `#assert_no_axioms` gate (one per
declaration, throws on any axiom) and a separate `#print axioms` cross-check over the headline declarations.
Each must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.BraidSignedAtom
#assert_no_axioms FX1Poly.Polygraph.braidSignedDeltaWord
#assert_no_axioms FX1Poly.Polygraph.braidSignedDeltaInverseWord
#assert_no_axioms FX1Poly.Polygraph.BraidThreeSignedConv
#assert_no_axioms FX1Poly.Polygraph.braidSignedDeltaInvDeltaCancel
#assert_no_axioms FX1Poly.Polygraph.braidSignedDeltaSecondRepCancel
#assert_no_axioms FX1Poly.Polygraph.braidSignedInverseBraidRel
#assert_no_axioms FX1Poly.Polygraph.braidSignedFlipDeltaInvSigmaOne
#assert_no_axioms FX1Poly.Polygraph.braidSignedFlipDeltaInvSigmaTwo
#assert_no_axioms FX1Poly.Polygraph.braidSignedInvExpandSigmaOne
#assert_no_axioms FX1Poly.Polygraph.braidSignedInvExpandSigmaTwo
#assert_no_axioms FX1Poly.Polygraph.braidSignedLawHolds
#assert_no_axioms FX1Poly.Polygraph.braidSignedCancelHolds
#assert_no_axioms FX1Poly.Polygraph.braidSignedDeltaInvDeltaWordCancel
#assert_no_axioms FX1Poly.Polygraph.fxBraid_hasSignedWordRelation

/-! ## Independent `#print axioms` cross-check — the derived complement toolkit -/

#print axioms FX1Poly.Polygraph.braidSignedDeltaInvDeltaCancel
#print axioms FX1Poly.Polygraph.braidSignedInverseBraidRel
#print axioms FX1Poly.Polygraph.braidSignedFlipDeltaInvSigmaOne
#print axioms FX1Poly.Polygraph.braidSignedFlipDeltaInvSigmaTwo
#print axioms FX1Poly.Polygraph.braidSignedInvExpandSigmaOne
#print axioms FX1Poly.Polygraph.braidSignedInvExpandSigmaTwo
#print axioms FX1Poly.Polygraph.fxBraid_hasSignedWordRelation

end FX1PolyAudit
