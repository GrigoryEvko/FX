import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidValleyProducer

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringPositiveMidValleyProducer — zero-axiom gate
(FC-3 r41)

Per-declaration zero-axiom gate for the positive-mid whole-valley `SpineTraceEquiv` producer: the block-level
headline `stringPositiveMidValleysWithEqualMatching_spineTraceEquiv` (which derives the four per-block facts from a
SINGLE whole-boundary matching equality via the shipped positive-covering append-split + telescopes, then feeds the
r40 block reassembly, gated on the ONE cup-sort brick), its genuine distinct-double-cup fire (relating two
syntactically DISTINCT spines `[0, 4] ≠ [2, 0]` with equal whole `matchingOfSpineList 2`), and the honesty marker.
Every declaration is public, so there are no private helpers to cover transitively.  Every declaration must be free
of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`.  The project
`#assert_no_axioms` macro is fuel-based; the independent `#print axioms` lines below are the trusted cross-check
(they catch a `decide` silently degraded to `sorryAx` and any `Lean.ofReduceBool` from `native_decide`). -/

namespace FX1PolyAudit

-- ★★ L2: the positive-mid whole-valley producer (append-split assembled, gated on the ONE cup-sort brick)
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidValleysWithEqualMatching_spineTraceEquiv

-- ★★ the genuine distinct-block fire (producer relates two DISTINCT spines, gated on the brick)
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidProducer_firesOnDistinctDoubleCup

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasPositiveMidValleyProducer

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringPositiveMidValleysWithEqualMatching_spineTraceEquiv
#print axioms FX1Poly.Polygraph.stringPositiveMidProducer_firesOnDistinctDoubleCup
#print axioms FX1Poly.Polygraph.fxString_hasPositiveMidValleyProducer

end FX1PolyAudit
