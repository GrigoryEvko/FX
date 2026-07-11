import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescExtractionClose

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescExtractionClose — zero-axiom gate (BRAUER r31 B3)

Per-declaration zero-axiom gate for the unconditional extraction close: the four-field close
(`extractDiagram_correctedWord_general`), the unconditional corrected target
(`foldRealizesTargetDiagramCorrected_general`), the general-path firings on the recon self-attacks, and the B3 marker.

Independent `#print axioms` (scratch) reported every decl as "does not depend on any axioms".  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- the unconditional extraction close (the loops field discharges the gate)
#assert_no_axioms FX1Poly.Polygraph.extractDiagram_correctedWord_general
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected_general

-- the close fired on the recon self-attacks through the general path
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected_general_monster
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected_general_adversarialB
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected_general_wildCapThrough
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagramCorrected_general_wildCrossThrough

-- the honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasUnconditionalExtractionClose

-- B4: the reconstruction masters' honest decision (additive)
#assert_no_axioms FX1Poly.Polygraph.reconstructionMasters_deliveredAdditive
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasReconstructionSideClosed

-- B5: THE GRAND LEDGER -- the r31 state rfl-conjunction + the #2013 endgame marker
#assert_no_axioms FX1Poly.Polygraph.brauerReconstructionClosure_r31State
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerR31Complete

end FX1PolyAudit
