import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescRankPositionDuality

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescRankPositionDuality — zero-axiom gate (BRAUER r26, the rank ↔
position duality keystone)

Per-declaration zero-axiom gate for the CUP / THROUGH keystone: the propext-free `Nat`-equality kit
(`natBeqSelfDuality`, `beqSelfTrueDuality`, `eqOfBeqTrueDuality`, `memBoolGetAtSelfDuality`), the value→position
roundtrip on distinct lists (`natIndexOfValue_natListGetAt_ofDistinct`), its range-permutation wrapper
(`natIndexOfValue_natListGetAt_ofPermutationOfRange`) and the CUP `permInverse` form
(`natListGetAtPermInverse_natListGetAt_ofPermutationOfRange`), and the ingredient marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natBeqSelfDuality
#assert_no_axioms FX1Poly.Polygraph.beqSelfTrueDuality
#assert_no_axioms FX1Poly.Polygraph.eqOfBeqTrueDuality
#assert_no_axioms FX1Poly.Polygraph.memBoolGetAtSelfDuality
#assert_no_axioms FX1Poly.Polygraph.natIndexOfValue_natListGetAt_ofDistinct
#assert_no_axioms FX1Poly.Polygraph.natIndexOfValue_natListGetAt_ofPermutationOfRange
#assert_no_axioms FX1Poly.Polygraph.natListGetAtPermInverse_natListGetAt_ofPermutationOfRange
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasRankPositionDuality

end FX1PolyAudit
