import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidMiddleDeterminism

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidMiddleDeterminismAudit — zero-axiom gate for the
perm-middle determinism adjudicated as a Coxeter word-problem: the width-2 involution + width-3 Yang-Baxter
determinism instances lifted to the star scope, with the general double-coset lemma walled (WP-PROP r6, #2033).

Per-declaration `#assert_no_axioms` on: the two decidable-end determinism instances (involution + Yang-Baxter,
convertibility + shared matrix); the decidable-ends bundle; and the B2 adjudication markers (including the two
`= false` residual markers, `CoxeterWordUnique` + Node C).

Independent `#print axioms` on the two star-scope determinism convertibilities closes the gate. -/

namespace FX1PolyAudit

-- The two decidable-end determinism instances.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidInvolutionDeterminismOverStar
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidInvolutionDeterminismMatrixShared
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidYangBaxterDeterminismOverStar
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidYangBaxterDeterminismMatrixShared
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermMiddleDeterminismDecidableEnds

-- The B2 adjudication markers (established + free/matrix-forced + the two residuals + the ledger).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_permMiddleDeterminismDecidableEnds
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_deltaMuStagesMatrixForced
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_determinismFreeAtElementaryConstructors
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_coxeterWordUniqueMinimalLemmaUnbuilt
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nodeCTransposeNeverBuilt
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_determinismRoundSixAdjudicationShipped

-- Independent (non-fuel) axiom prints on the star-scope determinism convertibilities.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidInvolutionDeterminismOverStar
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidYangBaxterDeterminismOverStar

end FX1PolyAudit
