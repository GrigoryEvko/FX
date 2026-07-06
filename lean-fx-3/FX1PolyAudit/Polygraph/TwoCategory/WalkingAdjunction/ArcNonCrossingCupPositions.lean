import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingCupPositions

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcNonCrossingCupPositions — zero-axiom gate

Per-declaration zero-axiom gate for the cup-step cyclic-position bookkeeping (cup rung D2a-iii,
part 1): the spliced open-wire length and the leg adjacency.  The hand-rolled clean
Nat-subtraction plumbing is covered transitively.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupNewOpenLength
#assert_no_axioms FX1Poly.Polygraph.arcCupLegsAdjacent

end FX1PolyAudit
