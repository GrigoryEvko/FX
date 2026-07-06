import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupObstructionOrbitReselected

/-! # FX1PolyAudit/…/ArcCupObstructionOrbitReselected — zero-axiom gate

Per-declaration zero-axiom gate for the positive counterpart to the pins-refutation:
`arcCupOrbitWitness_holds_onObstruction` — `ArcCupOrbitWitness` is inhabited on the canonical
cup-cancel obstruction by re-selecting the second cup (`cup@2` swaps through the head, landing at
window 0; the moved prefix reassembles `leftTail`, so every pin closes by `rfl`).  Must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupObstructionCupTwoAtom
#assert_no_axioms FX1Poly.Polygraph.arcCupOrbitWitness_holds_onObstruction
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupObstructionOrbitReselected

end FX1PolyAudit
