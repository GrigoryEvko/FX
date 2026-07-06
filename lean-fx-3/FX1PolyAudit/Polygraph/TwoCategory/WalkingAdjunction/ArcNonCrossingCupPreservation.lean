import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingCupPreservation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcNonCrossingCupPreservation — zero-axiom gate

Per-declaration zero-axiom gate for the cup-step token node classification (cup rung D2a-iii,
part 2): every valid boundary token of the spliced state is an old-zone read or a new cup leg.
The private read-membership plumbing is covered transitively.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupTokenNodeClass

end FX1PolyAudit
