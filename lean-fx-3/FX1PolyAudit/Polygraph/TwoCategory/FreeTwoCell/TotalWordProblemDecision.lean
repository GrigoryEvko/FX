import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TotalWordProblemDecision

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/TotalWordProblemDecision — zero-axiom gate

Per-declaration zero-axiom gate for the FREE-7 capstone: the computable class list,
its completeness, the un-gated chained-seed trace decision, the spine chainedness,
and the total front door.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.chainedSeedClassList
#assert_no_axioms FX1Poly.Polygraph.chainedSeedClassList_isComplete
#assert_no_axioms FX1Poly.Polygraph.decideAtomicTraceEquivOfChainedSeed
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spine_isBoundaryChained
#assert_no_axioms FX1Poly.Polygraph.decideTwoCellConvFull
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasUngatedFreeTwoCellDecision

end FX1PolyAudit
