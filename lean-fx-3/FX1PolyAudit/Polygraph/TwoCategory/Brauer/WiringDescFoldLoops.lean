import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFoldLoops

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescFoldLoops — zero-axiom gate (BRAUER r29 B3)

Per-declaration zero-axiom gate for T-CLOSE(b): the `partner` field (`extractDiagram_partner_correctedWord`), the
loops-gated four-field close (`extractDiagram_correctedWord_ofLoopsField`,
`foldRealizesTargetDiagramCorrected_ofLoopsField`), the decidable loops-field witnesses, the gated adversarial-B
close, and the honest loops wall marker `fxBrauer_hasFoldLoopsCorrectness`.

Independent `#print axioms` (in a scratch during development) reported every decl as "does not depend on any axioms".
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- Section 1: the partner field (the whole B2 dispatch, list-assembled)
#assert_no_axioms FX1Poly.Polygraph.extractDiagram_partner_correctedWord

-- Section 2: the loops-gated four-field close
#assert_no_axioms FX1Poly.Polygraph.extractDiagram_correctedWord_ofLoopsField
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected_ofLoopsField

-- Section 3: the decidable loops-field witnesses + the gated adversarial-B close
#assert_no_axioms FX1Poly.Polygraph.foldLoopsField_allLoop
#assert_no_axioms FX1Poly.Polygraph.foldLoopsField_adversarialB
#assert_no_axioms FX1Poly.Polygraph.foldLoopsField_monster
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected_adversarialB_viaGated

-- Section 4: the honest loops wall marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFoldLoopsCorrectness

end FX1PolyAudit
