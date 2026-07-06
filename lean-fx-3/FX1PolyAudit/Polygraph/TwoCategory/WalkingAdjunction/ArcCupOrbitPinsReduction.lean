import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupOrbitPinsReduction

/-! # FX1PolyAudit/…/ArcCupOrbitPinsReduction — zero-axiom gate

Per-declaration zero-axiom gate for the orbit-witness reduction: with the shipped locator discharging
the split, bubble, and `movedDomPin`, the full `ArcCupOrbitWitness` follows from `windowPin ∧ tailsCancel`
for the located cup — crisply isolating the cup-head discharge's open content as those two pins.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupOrbitWitness_ofWindowPinAndTailsCancel
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupOrbitPinsReduction

end FX1PolyAudit
