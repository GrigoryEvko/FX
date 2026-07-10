import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlide

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCupSlide — zero-axiom gate (WP-BRAUER-4 r4, B1)

Per-declaration zero-axiom gate for the V2 presentation change: the cup-slide DATA row (`cupSlideRelation`, the
∗-dual of `capSlideRelation`) with its `decide` diagram-soundness, the eight-relation V2 presentation
(`brauerPresentation8` = `brauerPresentation7 ++ [cupSlideRelation]`) with all-sound, the additive V2
over-approximation `BrauerConvFree8` (embedding `BrauerConvFree7` via `ofFree7`), the non-vacuity witnesses, and the
two honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the cup-slide DATA row + its diagram-soundness
#assert_no_axioms FX1Poly.Polygraph.cupSlideRelation
#assert_no_axioms FX1Poly.Polygraph.cupSlide_diagram_sound

-- the V2 presentation + all-sound
#assert_no_axioms FX1Poly.Polygraph.brauerPresentation8
#assert_no_axioms FX1Poly.Polygraph.brauerPresentation8_allSound

-- the V2 over-approximation + the V1-into-V2 embeddings
#assert_no_axioms FX1Poly.Polygraph.BrauerConvFree8
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree8_ofFree7
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree8_ofFree

-- non-vacuity: the cup-slide straddle IS derivable at V2, the V1 closure embeds, the row is proper
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree8_cupSlide_derivable
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree8_cupUntwist_seed
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree8_cupSlide_distinct

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerCupSlideRow
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerV2Presentation

end FX1PolyAudit
