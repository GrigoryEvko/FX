import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescWindowLocality

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescWindowLocality — zero-axiom gate (KEYSTONE4 leg 2)

Per-declaration zero-axiom gate for the `natListSliceAt` window-locality geometry: the reduction-equation
preamble, the append-skip-prefix / drop-shift decompositions, and the two input-node correspondence facts
(`natListSliceAt_spliceRight` = Fact A, `natListSliceAt_spliceLeftShift` = Fact B), plus the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- reduction-equation preamble
#assert_no_axioms FX1Poly.Polygraph.sliceAt_nil
#assert_no_axioms FX1Poly.Polygraph.sliceAt_count_zero
#assert_no_axioms FX1Poly.Polygraph.sliceAt_cons_succ
#assert_no_axioms FX1Poly.Polygraph.removeManyAt_zero
#assert_no_axioms FX1Poly.Polygraph.removeManyAt_succ_cons
#assert_no_axioms FX1Poly.Polygraph.insertAt_zero
#assert_no_axioms FX1Poly.Polygraph.splice_succ_cons

-- decompositions
#assert_no_axioms FX1Poly.Polygraph.natListSliceAt_appendSkipPrefix
#assert_no_axioms FX1Poly.Polygraph.natListSliceAt_dropShift

-- Fact A / Fact B
#assert_no_axioms FX1Poly.Polygraph.natListSliceAt_spliceRight
#assert_no_axioms FX1Poly.Polygraph.natListSliceAt_spliceLeftShift

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringDescWindowLocality

end FX1PolyAudit
