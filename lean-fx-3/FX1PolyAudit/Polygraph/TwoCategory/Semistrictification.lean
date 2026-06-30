import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Semistrictification

/-! # FX1PolyAudit/AuditTier0ModeSemistrictification — zero-axiom gate for mode-7

Per-declaration zero-axiom gate for `mode-7` (`FX1Poly/Tier0/Mode/Semistrictification.lean`): the Eckmann–Hilton
obstruction data + its full theorem (operations coincide, medial, commutativity, associativity), the trivial and
`Bool`-`&&` witnesses, the semistrict ω-category interface + the terminal instance, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The Eckmann–Hilton obstruction + the full theorem
#assert_no_axioms FX1Poly.Tier0.EckmannHilton
#assert_no_axioms FX1Poly.Tier0.EckmannHilton.op1_eq_op2
#assert_no_axioms FX1Poly.Tier0.EckmannHilton.medial
#assert_no_axioms FX1Poly.Tier0.EckmannHilton.op2_comm
#assert_no_axioms FX1Poly.Tier0.EckmannHilton.op2_assoc
#assert_no_axioms FX1Poly.Tier0.EckmannHilton.op1_comm

-- Witnesses (non-vacuity)
#assert_no_axioms FX1Poly.Tier0.trivialEckmannHilton
#assert_no_axioms FX1Poly.Tier0.boolAndEckmannHilton

-- The semistrict ω-category interface + instance
#assert_no_axioms FX1Poly.Tier0.SemistrictOmegaCategory
#assert_no_axioms FX1Poly.Tier0.terminalSemistrictOmegaCategory

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSimpsonSemistrictification
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSemistrictificationFunctor
#assert_no_axioms FX1Poly.Tier0.fxMode_hasStrictGroupoidHomotopyObstruction

end FX1PolyAudit
