import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapInternalCounts

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapInternalCounts — zero-axiom gate

Per-declaration zero-axiom gate for the internal-count list transports (peel campaign H,
rung E-3, part 10): the composite per-port internal cap/cup count lists are the fresh
lists with the consumed strand's values spliced in at the window position.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_internalCapCountsCorr
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_internalCupCountsCorr

end FX1PolyAudit
