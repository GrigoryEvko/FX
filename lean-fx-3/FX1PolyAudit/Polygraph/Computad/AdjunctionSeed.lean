import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Computad.AdjunctionSeed

/-! # FX1PolyAudit.Polygraph.Computad.AdjunctionSeed — zero-axiom gate for the walking-adjunction computad seed

Per-declaration zero-axiom gate for the canonical non-degenerate 2-computad witness
(`FX1Poly/Polygraph/Computad/AdjunctionSeed.lean`): the two-mode adjunction / cohesion seed
(`AdjunctionMode` / `AdjunctionModality` / `adjunctionGraph` / `adjunctionLeftThenRight` /
`adjunctionRightThenLeft` / `AdjunctionTwoCell` / `adjunctionModeSignature`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.AdjunctionMode
#assert_no_axioms FX1Poly.Polygraph.AdjunctionModality
#assert_no_axioms FX1Poly.Polygraph.adjunctionGraph
#assert_no_axioms FX1Poly.Polygraph.adjunctionLeftThenRight
#assert_no_axioms FX1Poly.Polygraph.adjunctionRightThenLeft
#assert_no_axioms FX1Poly.Polygraph.AdjunctionTwoCell
#assert_no_axioms FX1Poly.Polygraph.adjunctionModeSignature

end FX1PolyAudit
