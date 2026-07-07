import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyMatchingSpineTraceEquiv

/-! # FX1PolyAudit/…/ValleyMatchingSpineTraceEquiv — zero-axiom gate

Per-declaration zero-axiom gate for Piece II of the fib-3 gate: the cap-side internal cup-count free leg
(`pureCapSpine_internalCupCounts_eq_replicate`, `pureCapSpines_internalCupCountsAgree_ofDiagram`), the cap
tails-cancel dual (`pureCapTailsCancel_ofDiagramAndInternalCap`), and the assembled valley trace equivalence
`sameMatchingValleys_spineTraceEquiv`.  The private helpers (`cupCountReflect`, `capCountReflect`,
`extractArc_internalCupCounts_eq_replicate_of_cupNil`, `topCount_eq_openWiresLength`, the range/list plumbing)
are covered transitively — a `propext` leak there would surface on the public theorems asserted here.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.pureCapSpine_internalCupCounts_eq_replicate
#assert_no_axioms FX1Poly.Polygraph.pureCapSpines_internalCupCountsAgree_ofDiagram
#assert_no_axioms FX1Poly.Polygraph.pureCapTailsCancel_ofDiagramAndInternalCap
#assert_no_axioms FX1Poly.Polygraph.sameMatchingValleys_spineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasValleyMatchingSpineTraceEquivAssembly

end FX1PolyAudit
