import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadWindowSeparation

/-! # FX1PolyAudit/…/ArcCupHeadWindowSeparation — zero-axiom gate

Per-declaration zero-axiom gate for the head-cup window separation: two boundary-chained, cup-headed spines
whose head cups differ only in window share the whole boundary `DiagramType` and the cup/cap totals, yet are
separated by `internalCupCounts` — so the head window is recoverable from `arcStructureOf` but NOT from the
boundary matching alone.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineHeadWindowZero_isChained
#assert_no_axioms FX1Poly.Polygraph.spineHeadWindowTwo_isChained
#assert_no_axioms FX1Poly.Polygraph.spineHeadWindowZero_atomReadoff
#assert_no_axioms FX1Poly.Polygraph.spineHeadWindowTwo_atomReadoff
#assert_no_axioms FX1Poly.Polygraph.boundaryDiagram_isWindowBlind
#assert_no_axioms FX1Poly.Polygraph.cupCapTotals_areWindowBlind
#assert_no_axioms FX1Poly.Polygraph.internalCupCounts_separateHeadWindow
#assert_no_axioms FX1Poly.Polygraph.internalCapCounts_separateHeadWindow
#assert_no_axioms FX1Poly.Polygraph.arcStructures_differ_byHeadWindow
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupHeadWindowSeparation

end FX1PolyAudit
