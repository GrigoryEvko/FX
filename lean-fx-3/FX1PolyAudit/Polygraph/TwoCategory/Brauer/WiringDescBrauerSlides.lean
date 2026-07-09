import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerSlides

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBrauerSlides — zero-axiom gate (BREACH r4 P2 slides)

Per-declaration zero-axiom gate for the EXTRACT slide moves: the distant cup/cap-past-generator commutes (via the
generic interchange constructor) and the adjacent-straddle cup-slide finding (the minimal diagram-equal instance +
its equal-parity non-falsifiability).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- Distant slides (interchange-derived)
#assert_no_axioms FX1Poly.Polygraph.distantCupCrossingSlideFree
#assert_no_axioms FX1Poly.Polygraph.distantCupCapSlideFree
#assert_no_axioms FX1Poly.Polygraph.distantCupCupSlideFree
#assert_no_axioms FX1Poly.Polygraph.distantCrossingCupSlideFree
#assert_no_axioms FX1Poly.Polygraph.distantCupCrossingSlideFree_inContext
#assert_no_axioms FX1Poly.Polygraph.distantCupCrossingSlideFree_smoke
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasDistantSlideMoves

-- The straddle finding
#assert_no_axioms FX1Poly.Polygraph.cupSlideStraddle_diagramEq
#assert_no_axioms FX1Poly.Polygraph.cupSlideStraddle_isBrauerConv
#assert_no_axioms FX1Poly.Polygraph.cupSlideStraddle_parity_eq
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCupSlideStraddleFinding

end FX1PolyAudit
