import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadFrontedReselection

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupHeadFrontedReselection — zero-axiom gate

Per-declaration zero-axiom gate for the swap-NF cup-case discharge: `cupHeadExtractionConclusion_ofFrontedHeadReselection`
derives the entire cup-case head extraction from the interchanger fronting (`AtomicTraceEquiv secondList
(headAtom :: movedRest)`) + the tail reselection (`AtomicTraceEquiv tailList movedRest`), with `tailsCancel`
free and NO `BubblesToFront` bookkeeping — the FM convergent swap-normal-form at cup granularity.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupHeadExtractionConclusion_ofFrontedHeadReselection
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupHeadFrontedReselection

end FX1PolyAudit
