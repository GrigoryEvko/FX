import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.NotSpuriousTrioOverQuotientAdjudication

/-! # FX1PolyAudit.Polygraph.Omega.NotSpuriousTrioOverQuotientAdjudicationAudit — zero-axiom gate for the
not-spurious trio's latent over-quotient adjudication (OMEGA SWEEP r2, B1).

Per-declaration `#assert_no_axioms` on: the three `Mat(N)` evaluations + generator tables; the four
separations; the four over-quotient witnesses; the idempotent's restored-soundness sub-theory (the genuine
`M`-mediated associativity legs + respect, the sound-row inductive, the matrix-eq relation, the
respects-congruence datum, restored soundness, the non-convertibility lemma and the strict-coarsening witness);
the valley control; the trio verdict markers.

Independent `#print axioms` (NOT fuel-based, MEMORY: mandatory) on the four decisive separations, the four
over-quotient witnesses, the idempotent restored soundness and the strict over-quotient closes the gate. -/

namespace FX1PolyAudit

-- B1 — the three Mat(N) evaluations + generator tables.
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionOmegaEvalGen
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionOmegaEvalCell
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaEvalGen
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaEvalCell
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEvalGen
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEvalCell

-- B1 — the four separations.
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionOmegaMatSeparatesSss
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaMatSeparatesSsss
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaMatSeparatesSssss
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaMatSeparatesEee

-- B1 — the four over-quotient witnesses + the idempotent valley control.
#assert_no_axioms FX1Poly.Polygraph.Omega.involutionOmegaBaseRelOverQuotientsSss
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaBaseRelOverQuotientsSsss
#assert_no_axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaBaseRelOverQuotientsSssss
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaBaseRelOverQuotientsEee
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaEeeValleyLiterallyEqual

-- B1 — the idempotent restored-soundness sub-theory.
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaGenuineAssocLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaGenuineAssocRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaMatrixRespectsGenuineAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.IdempotentSemigroupOmegaSoundRow
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaMatrixEq
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaSoundMatrixEvalAbsorbs
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaMatrixSoundOverSound
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaSoundRowNotConvertibleEee
#assert_no_axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaBaseRelStrictlyOverQuotientsSound

-- B1 / B4 — the trio verdict markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_involutionOverQuotientConfirmedMatNSeparated
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_cyclicThreeOverQuotientConfirmedMatNSeparated
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_idempotentOverQuotientConfirmedMatNSeparated
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_trioTorsionModelCategoryErrorRetracted
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_involutionCyclicSoundSubTheoryIsStrictFubiniWalled
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_idempotentSoundSubTheoryIsMMediatedAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_notSpuriousTrioOverQuotientAdjudicationShipped

-- Independent confirmation (not fuel-based): the decisive facts are all axiom-free.
#print axioms FX1Poly.Polygraph.Omega.involutionOmegaMatSeparatesSss
#print axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaMatSeparatesSsss
#print axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaMatSeparatesSssss
#print axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaMatSeparatesEee
#print axioms FX1Poly.Polygraph.Omega.involutionOmegaBaseRelOverQuotientsSss
#print axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaBaseRelOverQuotientsSsss
#print axioms FX1Poly.Polygraph.Omega.cyclicThreeOmegaBaseRelOverQuotientsSssss
#print axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaBaseRelOverQuotientsEee
#print axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaMatrixSoundOverSound
#print axioms FX1Poly.Polygraph.Omega.idempotentSemigroupOmegaBaseRelStrictlyOverQuotientsSound

end FX1PolyAudit
