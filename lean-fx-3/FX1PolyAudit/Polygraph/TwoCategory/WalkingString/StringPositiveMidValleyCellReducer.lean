import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidValleyCellReducer

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringPositiveMidValleyCellReducer — zero-axiom gate
(FC-3 r42, the positive-mid valley determinacy cell reducer, L3)

Per-declaration zero-axiom gate for the cell-level reducer inhabiting `StringCellValleyTraceEquivPositive` over the
walking ADJOINT-TRIPLE signature, GATED on the ONE cup-sort brick `StringPositiveMidPureCupDeterminacy`: the L3
reducer `stringPositiveMidValleyTraceEquiv_holds` (block-split + word derivation over the r41 producer, with the
shared `midWord` obtained via the BRICK-FREE cap-trace route), and the three brick→master implications
(`stringMatchingReductsShareSpineTrace_ofBrick`, `stringConvOfMapEq_ofBrick`, `decidableStringSaturatedConv_ofBrick`)
that compose the reducer with the r39 one-sub-producer beam — collapsing the whole #2020 residual to the single
brick — plus the honesty marker.  The private helpers (`stringPositiveMidReducerRangeLength`,
`stringPositiveMidReducerRangeLoopLength`) are covered transitively by the public theorems that consume them.  Every
declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`.  The
project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` lines below are the trusted
cross-check (they catch a `decide` silently degraded to `sorryAx` and any `Lean.ofReduceBool` from `native_decide`). -/

namespace FX1PolyAudit

-- ★★ L3: the positive-mid valley CELL reducer (gated on the ONE cup-sort brick)
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidValleyTraceEquiv_holds

-- ★ the brick→master implications (whole #2020 residual collapses to the single brick)
#assert_no_axioms FX1Poly.Polygraph.stringMatchingReductsShareSpineTrace_ofBrick
#assert_no_axioms FX1Poly.Polygraph.stringConvOfMapEq_ofBrick
#assert_no_axioms FX1Poly.Polygraph.decidableStringSaturatedConv_ofBrick

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasPositiveMidValleyCellReducer

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringPositiveMidValleyTraceEquiv_holds
#print axioms FX1Poly.Polygraph.stringMatchingReductsShareSpineTrace_ofBrick
#print axioms FX1Poly.Polygraph.stringConvOfMapEq_ofBrick
#print axioms FX1Poly.Polygraph.decidableStringSaturatedConv_ofBrick
#print axioms FX1Poly.Polygraph.fxString_hasPositiveMidValleyCellReducer

end FX1PolyAudit
