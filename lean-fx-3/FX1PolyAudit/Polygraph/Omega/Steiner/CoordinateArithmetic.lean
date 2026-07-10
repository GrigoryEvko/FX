import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.CoordinateArithmetic

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/CoordinateArithmetic — zero-axiom gate (OMEGA-2 B-arith kit)

Per-declaration `#assert_no_axioms` on the abelian-group kit for equal-length coordinate chains: the
degenerate identity table, the nil absorbers, commutativity / associativity / length-preservation, and
the two zero-unit laws.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Steiner.zeroVector
#assert_no_axioms FX1Poly.Polygraph.Steiner.zeroVector_length
#assert_no_axioms FX1Poly.Polygraph.Steiner.addCoordinates_nil_left
#assert_no_axioms FX1Poly.Polygraph.Steiner.addCoordinates_nil_right
#assert_no_axioms FX1Poly.Polygraph.Steiner.addCoordinates_comm
#assert_no_axioms FX1Poly.Polygraph.Steiner.addCoordinates_assoc
#assert_no_axioms FX1Poly.Polygraph.Steiner.addCoordinates_length_eq
#assert_no_axioms FX1Poly.Polygraph.Steiner.addCoordinates_zeroVector_left
#assert_no_axioms FX1Poly.Polygraph.Steiner.addCoordinates_zeroVector_right
#assert_no_axioms FX1Poly.Polygraph.Steiner.negateCoordinates_zeroVector
#assert_no_axioms FX1Poly.Polygraph.Steiner.subtractCoordinates_zeroVector_right

end FX1PolyAudit
