import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFlatDescriptorCoverage

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescFlatDescriptorCoverage — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER r44 Q2 (loop-fate prepend + honest JAM-B partial) + Q4 (coverage census):
the loop-fate threading through the outer sink-step combinator, the honest JAM-B `none`, the combined dispatch, the
coverage census + its classifier tie, the honesty markers, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the census pins are pure
`classifyFirstCupNeighbour` / extractor reductions (no `decide` over `brauerDiagramOf`), the combined dispatch is a
full-enum `Option` chain (no wildcard), and `prepend_preserves_loopFate` is `rfl` on the `.loop` arm of `prepend`.
Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.prepend_preserves_loopFate
#assert_no_axioms FX1Poly.Polygraph.jamB_staysNone
#assert_no_axioms FX1Poly.Polygraph.flatRegionDispatchCombined
#assert_no_axioms FX1Poly.Polygraph.flatDispatch_coverageCensus
#assert_no_axioms FX1Poly.Polygraph.coverageCensus_classifierTie
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFlatDispatchCoverageCensus
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFlatDispatchTotalityGap
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_flatDispatchCoverageCensusTerminalState

end FX1PolyAudit
