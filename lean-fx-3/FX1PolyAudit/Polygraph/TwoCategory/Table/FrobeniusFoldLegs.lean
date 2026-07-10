import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusFoldLegs

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.FrobeniusFoldLegs — zero-axiom gate for the deep-`foldEq`
shift algebra + the connectivity->partition reduction (FROB-RESUME r2, #2017).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`.
The private `List.range` / `firstIndexWithRoot` scan primitives + `mapConstZero` are covered transitively through
`spiderPartition_of_allConnected`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.shiftBrauerWord_zero
#assert_no_axioms FX1Poly.Polygraph.shiftBrauerWord_add
#assert_no_axioms FX1Poly.Polygraph.spiderPartition_of_allConnected
#assert_no_axioms FX1Poly.Polygraph.canonicalSpider22_allConnected
#assert_no_axioms FX1Poly.Polygraph.extraSpider22_via_connectivityReduction
#assert_no_axioms FX1Poly.Polygraph.fxTab_hasFoldLegShiftAlgebra

end FX1PolyAudit
