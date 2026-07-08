import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConv

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescConv — zero-axiom gate (KEYSTONE6 brick B)

Per-declaration zero-axiom gate for the diagram-sound convertibility relation `BrauerConv`: the fold-split
(`processBrauer_append`), the soundness theorem (`brauerConv_sound`), the non-vacuity witnesses
(`brauerConv_yangBaxter`, `brauerDiagram_crossing_ne_identity`, `brauerConv_crossing_not_identity`), and the
honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the fold-split + the soundness theorem
#assert_no_axioms FX1Poly.Polygraph.processBrauer_append
#assert_no_axioms FX1Poly.Polygraph.brauerConv_sound

-- non-vacuity: distinct related words, separating discriminator, proper relation
#assert_no_axioms FX1Poly.Polygraph.brauerConv_yangBaxter
#assert_no_axioms FX1Poly.Polygraph.brauerDiagram_crossing_ne_identity
#assert_no_axioms FX1Poly.Polygraph.brauerConv_crossing_not_identity

-- the contextual whisker (congruence) move: NON-VACUOUS witness (transitively covers the private
-- `relationAgrees` helper) + the distinctness of the whiskered words
#assert_no_axioms FX1Poly.Polygraph.brauerConv_whisker_crossingInvolution_inContext
#assert_no_axioms FX1Poly.Polygraph.brauerConv_whisker_inContext_distinct

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerConvSoundness
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerConvContextualInterchange
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerWhiskerMove
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerSoundnessResidualNamed

end FX1PolyAudit
