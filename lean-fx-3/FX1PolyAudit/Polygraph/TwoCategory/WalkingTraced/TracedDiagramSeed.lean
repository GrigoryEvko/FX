import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingTraced.TracedDiagramSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingTraced.TracedDiagramSeed — zero-axiom gate (the walking traced PROP signature + trace-axiom relation)

Per-declaration zero-axiom gate for the walking traced PROP seed: the `TracedDiagram` carrier, the
`TracedGenerator` genuine generator, the boundary-signature `TracedSignature` / `tracedBoxSignature` and their
smokes, the concrete sample diagrams, and the trace-axiom diagram `TracedDiagramConv` convertibility with its
vanishing-I / yanking / left-tightening / whiskered witnesses.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.TracedDiagram
#assert_no_axioms FX1Poly.Polygraph.TracedGenerator
#assert_no_axioms FX1Poly.Polygraph.TracedSignature
#assert_no_axioms FX1Poly.Polygraph.tracedBoxSignature
#assert_no_axioms FX1Poly.Polygraph.tracedBoxSignature_oneOne
#assert_no_axioms FX1Poly.Polygraph.tracedBoxSignature_twoTwo
#assert_no_axioms FX1Poly.Polygraph.tracedBoxSignature_zeroZero
#assert_no_axioms FX1Poly.Polygraph.tracedSwapDiagram
#assert_no_axioms FX1Poly.Polygraph.tracedBoxDiagram
#assert_no_axioms FX1Poly.Polygraph.tracedYankingLeft
#assert_no_axioms FX1Poly.Polygraph.tracedVanishingBoxLeft
#assert_no_axioms FX1Poly.Polygraph.tracedTighteningLeft
#assert_no_axioms FX1Poly.Polygraph.tracedTighteningRight
#assert_no_axioms FX1Poly.Polygraph.TracedDiagramConv
#assert_no_axioms FX1Poly.Polygraph.tracedVanishingUnitHolds
#assert_no_axioms FX1Poly.Polygraph.tracedYankingHolds
#assert_no_axioms FX1Poly.Polygraph.tracedLeftTighteningHolds
#assert_no_axioms FX1Poly.Polygraph.tracedYankingWhiskeredHolds

end FX1PolyAudit
