import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreeSignedCanon

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingBraid.BraidThreeSignedCanon — zero-axiom gate (the signed Garside canon + transducer)

Per-declaration zero-axiom gate for the signed braid-group brick 2: the Int-free two-constructor canon
carrier with its manual `decEq`, the mutually-inverse `Δ`-moves and their factor-transparency, the
negative-shift positive-atom carry (structural on the bare `Nat`) with its definitional-reduction tripwire,
THE COMMUTATION `P_a ∘ Δ⁻¹ = Δ⁻¹ ∘ P_τ(a)` and its two evaluated specializations, the signed transducer and
normalizer with defining equations, the greedy-preservation chain, the `Δ`-factorization of the shipped
positive transducer (both orders), the cons-only signed readback, the canon value smokes, and the
established marker.

Two independent mechanisms per the AuditAll-semantics rule: the fuel-based `#assert_no_axioms` gate (one per
declaration, throws on any axiom) and a separate `#print axioms` cross-check over the headline declarations.
Each must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.BraidSignedCanon
#assert_no_axioms FX1Poly.Polygraph.braidSignedCanonDecEq
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqBraidSignedCanon
#assert_no_axioms FX1Poly.Polygraph.braidSignedCanonFactors
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependDeltaInv
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependDelta
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependDeltaInv_prependDelta
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependDelta_prependDeltaInv
#assert_no_axioms FX1Poly.Polygraph.braidSignedCanonFactors_prependDeltaInv
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtomWithShift
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtomWithShift_succ
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtom
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtom_prependDeltaInv_comm
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaOne
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtom_prependDeltaInv_commSigmaTwo
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependAtom
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord_nil
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord_cons
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtomWithShift_preservesGreedy
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtom_preservesGreedy
#assert_no_axioms FX1Poly.Polygraph.braidSignedPrependAtom_preservesGreedy
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord_greedy
#assert_no_axioms FX1Poly.Polygraph.braidPrependAtom_deltaFactorization
#assert_no_axioms FX1Poly.Polygraph.braidPrependAtom_deltaFactorizationSwapped
#assert_no_axioms FX1Poly.Polygraph.braidSignedAtomOfPositiveAtom
#assert_no_axioms FX1Poly.Polygraph.braidSignedFactorWordOnto
#assert_no_axioms FX1Poly.Polygraph.braidSignedReadbackFactors
#assert_no_axioms FX1Poly.Polygraph.braidSignedDeltaPow
#assert_no_axioms FX1Poly.Polygraph.braidSignedDeltaInvPow
#assert_no_axioms FX1Poly.Polygraph.braidSignedReadbackCanon
#assert_no_axioms FX1Poly.Polygraph.braidSignedReadbackCanon_deltaOne
#assert_no_axioms FX1Poly.Polygraph.braidSignedReadbackCanon_deltaInvOne
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord_emptyWord
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord_sigmaOneInv
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord_sigmaTwoInv
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord_deltaInverseWord
#assert_no_axioms FX1Poly.Polygraph.braidSignedNormalizeWord_deltaWord
#assert_no_axioms FX1Poly.Polygraph.fxBraid_hasSignedGarsideCanon

/-! ## Independent `#print axioms` cross-check — the commutation, the normalizer, the Δ-factorization -/

#print axioms FX1Poly.Polygraph.braidSignedCanonDecEq
#print axioms FX1Poly.Polygraph.braidSignedPrependPositiveAtom_prependDeltaInv_comm
#print axioms FX1Poly.Polygraph.braidSignedPrependDeltaInv_prependDelta
#print axioms FX1Poly.Polygraph.braidSignedNormalizeWord
#print axioms FX1Poly.Polygraph.braidSignedNormalizeWord_greedy
#print axioms FX1Poly.Polygraph.braidPrependAtom_deltaFactorization
#print axioms FX1Poly.Polygraph.braidPrependAtom_deltaFactorizationSwapped
#print axioms FX1Poly.Polygraph.braidSignedReadbackCanon
#print axioms FX1Poly.Polygraph.fxBraid_hasSignedGarsideCanon

end FX1PolyAudit
