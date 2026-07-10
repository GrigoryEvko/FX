import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlideExtract

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCupSlideExtract — zero-axiom gate (WP-BRAUER-4 r4, B3)

Per-declaration zero-axiom gate for the V2 extraction-fold MOVE SET: the contextual cup-slide primitive
(`cupSlideStraddleFree8_inContext`), the distant slides lifted to `BrauerConvFree8`, the untwist-normalization seed,
the crossing-block straightening engine, the composite cup-sink demonstration, and the two honesty markers (the
move-set completion + the honestly-`false` extraction-fold residual).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the new cup-sink primitive (contextual straddle slide)
#assert_no_axioms FX1Poly.Polygraph.cupSlideStraddleFree8_inContext

-- the distant slides lifted to BrauerConvFree8
#assert_no_axioms FX1Poly.Polygraph.distantCupCrossingSlideFree8
#assert_no_axioms FX1Poly.Polygraph.distantCupCapSlideFree8
#assert_no_axioms FX1Poly.Polygraph.distantCupCupSlideFree8

-- the untwist-normalization seed + the crossing-block straightening engine
#assert_no_axioms FX1Poly.Polygraph.untwistNormalize_conv8
#assert_no_axioms FX1Poly.Polygraph.untwistNF_conv8
#assert_no_axioms FX1Poly.Polygraph.crossingWords_equalPerm_conv8

-- the composite cup-sink demonstration (V1-impossible reduction)
#assert_no_axioms FX1Poly.Polygraph.cupSink_composite_demo

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCupSinkMoveSet
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerV2ExtractionFold

end FX1PolyAudit
