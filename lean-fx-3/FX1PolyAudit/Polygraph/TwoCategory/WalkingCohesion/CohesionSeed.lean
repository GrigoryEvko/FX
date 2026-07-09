import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCohesion.CohesionSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingCohesion.CohesionSeed — zero-axiom gate (the cohesion seed)

Per-declaration zero-axiom gate for the walking-cohesion seed: the mode / modality / two-cell generator
inductives, the 1-cell generators and composites, the signature, and the freeness smokes.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.CohesionMode
#assert_no_axioms FX1Poly.Polygraph.CohesionModality
#assert_no_axioms FX1Poly.Polygraph.cohesionGraph
#assert_no_axioms FX1Poly.Polygraph.cohesionShape
#assert_no_axioms FX1Poly.Polygraph.cohesionFlat
#assert_no_axioms FX1Poly.Polygraph.cohesionSharp
#assert_no_axioms FX1Poly.Polygraph.cohesionShapeShape
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatFlat
#assert_no_axioms FX1Poly.Polygraph.cohesionSharpSharp
#assert_no_axioms FX1Poly.Polygraph.cohesionShapeFlat
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatShape
#assert_no_axioms FX1Poly.Polygraph.cohesionFlatSharp
#assert_no_axioms FX1Poly.Polygraph.cohesionSharpFlat
#assert_no_axioms FX1Poly.Polygraph.CohesionTwoCell
#assert_no_axioms FX1Poly.Polygraph.cohesionModeSignature
#assert_no_axioms FX1Poly.Polygraph.cohesionShape_length
#assert_no_axioms FX1Poly.Polygraph.cohesionShapeFlat_length
#assert_no_axioms FX1Poly.Polygraph.cohesionSharpFlat_length
#assert_no_axioms FX1Poly.Polygraph.cohesionShape_ne_flat
#assert_no_axioms FX1Poly.Polygraph.cohesionFlat_ne_sharp
#assert_no_axioms FX1Poly.Polygraph.cohesionShape_ne_sharp

end FX1PolyAudit
