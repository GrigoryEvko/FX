-- TODO: DELETE THIS GARBAGE -- defective bunchedBimonoid star (refuted r29/r30/r31); superseded by the LafontProp re-founding
import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidWhiskerOneCellCoherenceWall

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidWhiskerOneCellCoherenceWallAudit — zero-axiom gate for the
r18 T2 coherence adjudication: the three whisker-vs-1-cell coherences (associator / identity-unitor / whisker-commute)
are matrix-sound and non-boundary-parallel, WALLED out of `StrictAxiomRel` (`StrictAxioms.lean` byte-intact).

Per-declaration `#assert_no_axioms` on every matrix-soundness `rfl`, the boundary-source pins, the non-parallelism
disequalities, the boundary-parallel contrast, and the marker, PLUS independent (non-fuel) `#print axioms` on a
matrix-soundness leg, the associator non-parallelism, and the marker. -/

namespace FX1PolyAudit

-- W1 — the five matrix-soundness legs.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerOneCellAssocLeftMatrixSound
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerOneCellAssocRightMatrixSound
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerOneCellUnitorLeftMatrixSound
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerOneCellUnitorRightMatrixSound
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerOneCellCommuteMatrixSound

-- W2 — the boundary-source pins, the non-parallelism disequalities, the boundary-parallel contrast.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerOneCellAssocSourceLHS
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerOneCellAssocSourceRHS
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerOneCellAssocSourcesNotParallel
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerOneCellUnitorSourcesNotParallel
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidVcompAssocBoundaryParallel

-- W3 — the WP-PROP-owned residual marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_whiskerOneCellCoherencesWalledNotLanded

-- Independent (non-fuel) axiom prints on a matrix-soundness leg, the associator non-parallelism, and the marker.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerOneCellAssocLeftMatrixSound
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerOneCellAssocSourcesNotParallel
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerOneCellUnitorSourcesNotParallel
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_whiskerOneCellCoherencesWalledNotLanded

end FX1PolyAudit
