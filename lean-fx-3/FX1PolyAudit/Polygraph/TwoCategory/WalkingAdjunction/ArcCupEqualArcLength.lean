import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupEqualArcLength

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupEqualArcLength — zero-axiom gate

Per-declaration zero-axiom gate for the fixed-length sharpening: `equalArcSpine_length_eq` derives that two
cup/cap-seed spines with equal `arcStructureOfSpineList` have equal `List.length` (the arc structure pins both
`cupCount` and `capCount`, which partition the length at the seed), and
`mixedTailArcCompleteness_lengthObligation_discharged` reads that off for the length-preserving `SpineTraceEquiv`
conclusion of `MixedTailArcCompleteness` — excluding the length-changing snake / reduced-representative detour
inside every re-selection instance and pinning the residual to the fixed-length interchange completeness.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.equalArcSpine_length_eq
#assert_no_axioms FX1Poly.Polygraph.mixedTailArcCompleteness_lengthObligation_discharged
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupEqualArcLength

end FX1PolyAudit
