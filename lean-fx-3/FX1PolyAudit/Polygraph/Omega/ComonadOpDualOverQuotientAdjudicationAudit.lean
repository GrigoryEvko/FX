import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ComonadOpDualOverQuotientAdjudication

/-! # FX1PolyAudit.Polygraph.Omega.ComonadOpDualOverQuotientAdjudicationAudit — zero-axiom gate for the walking
comonad's op-dual over-quotient adjudication (OMEGA SWEEP r2, B3).

Per-declaration `#assert_no_axioms` on: the direct comonad transpose evaluation + generator table; the three
genuine-comonad-law respects; the three transpose separations; the three op-dual over-quotient witnesses + the
genuine-law-modelled-row-separated capstone; the verdict / census markers.

Independent `#print axioms` (NOT fuel-based, MEMORY: mandatory) on the three over-quotient witnesses and the
capstone closes the gate. -/

namespace FX1PolyAudit

-- B3 — the direct comonad transpose evaluation + generator table.
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaEvalGen
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaEvalCell

-- B3 — the three genuine-comonad-law respects (the sound-model evidence).
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaMatrixRespectsGenuineCounit
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaMatrixRespectsGenuineCounitRight
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaMatrixRespectsGenuineCoassoc

-- B3 — the three transpose separations.
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaMatSeparatesUnitUnit
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaMatSeparatesLeftUnitAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaMatSeparatesRightUnitAssoc

-- B3 — the three op-dual over-quotient witnesses + the capstone.
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaBaseRelOverQuotientsUnitUnit
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaBaseRelOverQuotientsLeftUnitAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaBaseRelOverQuotientsRightUnitAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.comonadOmegaGenuineLawRespectedRowSeparated

-- B3 — the verdict / census markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_comonadOverQuotientConfirmedTransposeSeparated
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_comonadEvalSoundOnGenuineComonadLaws
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_kzCoKzRideMonadComonadFreeRiders
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_comonadFullSoundnessTransposeFubiniWalled
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_comonadOpDualOverQuotientAdjudicationShipped

-- Independent confirmation (not fuel-based): the decisive facts are all axiom-free.
#print axioms FX1Poly.Polygraph.Omega.comonadOmegaBaseRelOverQuotientsUnitUnit
#print axioms FX1Poly.Polygraph.Omega.comonadOmegaBaseRelOverQuotientsLeftUnitAssoc
#print axioms FX1Poly.Polygraph.Omega.comonadOmegaBaseRelOverQuotientsRightUnitAssoc
#print axioms FX1Poly.Polygraph.Omega.comonadOmegaGenuineLawRespectedRowSeparated

end FX1PolyAudit
