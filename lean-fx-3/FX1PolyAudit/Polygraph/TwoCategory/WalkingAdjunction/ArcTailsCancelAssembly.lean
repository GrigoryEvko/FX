import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcTailsCancelAssembly

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcTailsCancelAssembly — zero-axiom gate

Per-declaration zero-axiom gate for the cup cancel's field-decomposition seam: a `FullArcStructure`
equality from its five field-agreements, and the `tailsCancel`-shaped wrapper splitting the cup cancel
into the diagram leg (parity campaign) and the four count legs (the orbit).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.FullArcStructure.eq_of_fields
#assert_no_axioms FX1Poly.Polygraph.arcCupTailsCancel_ofDiagramAndCounts
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcTailsCancelAssembly

end FX1PolyAudit
