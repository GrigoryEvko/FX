import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.SteinerFoundation.CellCoordinates

/-! # FX1PolyAudit/Polygraph/Steiner/CellCoordinates — zero-axiom gate

Per-declaration zero-axiom gate for the coordinate cell: vector add/negate/subtract, the
`ofNat`/`negSucc` constructor sign-split (positive/negative clamp), source/target as the
d-split, and the vector-arithmetic composition.  Init + ComputerAlgebra only.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Steiner.SteinerCell
#assert_no_axioms FX1Poly.Polygraph.Steiner.SteinerCell.HasDimensionShape
#assert_no_axioms FX1Poly.Polygraph.Steiner.addCoordinates
#assert_no_axioms FX1Poly.Polygraph.Steiner.negateCoordinates
#assert_no_axioms FX1Poly.Polygraph.Steiner.subtractCoordinates
#assert_no_axioms FX1Poly.Polygraph.Steiner.positiveClampEntry
#assert_no_axioms FX1Poly.Polygraph.Steiner.negativeClampEntry
#assert_no_axioms FX1Poly.Polygraph.Steiner.mapPositivePart
#assert_no_axioms FX1Poly.Polygraph.Steiner.mapNegativePart
#assert_no_axioms FX1Poly.Polygraph.Steiner.sourceOfCell
#assert_no_axioms FX1Poly.Polygraph.Steiner.targetOfCell
#assert_no_axioms FX1Poly.Polygraph.Steiner.composeAtDimension

end FX1PolyAudit
