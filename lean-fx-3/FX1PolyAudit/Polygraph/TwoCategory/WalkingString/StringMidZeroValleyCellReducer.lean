import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMidZeroValleyCellReducer

/-! # FX1PolyAudit/…/WalkingString/StringMidZeroValleyCellReducer — zero-axiom gate
(FC-3 r38, the mid-width-`0` valley determinacy cell reducer)

Per-declaration zero-axiom gate for the cell-level reducer inhabiting `StringMidZeroValleyTraceEquiv` over the
walking ADJOINT-TRIPLE signature: Brick A `stringSpineBoundaryChained_cupSuffix_ofCapPrefix` (the numeric cup-suffix
chain restriction), Brick B `spineBoundaryWordChained_cupSuffix_ofCapPrefix` (the word-chain drop), the reducer
`stringMidZeroValleyTraceEquiv_holds`, the cross-level truth-probe
`stringMidZeroValleyTraceEquiv_firesOnCrossLevelValley`, and the honesty marker.  The private helpers
(`stringMidZeroReducerRangeLength`, `stringMidZeroReducerRangeLoopLength`) are covered transitively by the public
theorems that consume them.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` lines
below are the trusted cross-check. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringSpineBoundaryChained_cupSuffix_ofCapPrefix
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryWordChained_cupSuffix_ofCapPrefix
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroValleyTraceEquiv_holds
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroValleyTraceEquiv_firesOnCrossLevelValley
#assert_no_axioms FX1Poly.Polygraph.fxString_hasMidZeroValleyCellReducer

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringSpineBoundaryChained_cupSuffix_ofCapPrefix
#print axioms FX1Poly.Polygraph.spineBoundaryWordChained_cupSuffix_ofCapPrefix
#print axioms FX1Poly.Polygraph.stringMidZeroValleyTraceEquiv_holds
#print axioms FX1Poly.Polygraph.stringMidZeroValleyTraceEquiv_firesOnCrossLevelValley
#print axioms FX1Poly.Polygraph.fxString_hasMidZeroValleyCellReducer

end FX1PolyAudit
