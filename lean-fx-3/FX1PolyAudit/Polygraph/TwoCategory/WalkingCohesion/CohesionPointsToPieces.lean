import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCohesion.CohesionPointsToPieces

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingCohesion.CohesionPointsToPieces — zero-axiom gate (the residual)

Per-declaration zero-axiom gate for the points-to-pieces transform: the transform cell, its size / cross-modality
smokes, the two law-detour identifications, and the markers (the residual honesty flag included).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cohesionPointsToPiecesCell
#assert_no_axioms FX1Poly.Polygraph.cohesionPointsToPiecesCell_size
#assert_no_axioms FX1Poly.Polygraph.cohesionPointsToPieces_crossModality
#assert_no_axioms FX1Poly.Polygraph.cohesionPtp_flatCounitLawDetour
#assert_no_axioms FX1Poly.Polygraph.cohesionPtp_shapeUnitLawDetour
#assert_no_axioms FX1Poly.Polygraph.fxCohesion_hasPointsToPiecesTransform
#assert_no_axioms FX1Poly.Polygraph.fxCohesion_hasCrossModalityThinness

end FX1PolyAudit
