import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcGodementSoundnessPeel

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcGodementSoundnessPeel — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the Godement arc soundness closed at the walking adjunction via the shipped
peel: the soundness theorem (`arcStructureOf_sound_of_convFull_adjunction` — `TwoCellConvFull → arc extract
equality`, no freshness residual, `0 < sourcePath.length`), the decision corollary
(`decidableTwoCellConvFull_of_adjunction`), and the two honesty markers.  The `private` range-length helpers are
covered transitively by these public declarations' closures.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the orchestrator does the unified registration). -/

namespace FX1PolyAudit

-- the soundness side closed via the peel + the decision corollary
#assert_no_axioms FX1Poly.Polygraph.arcStructureOf_sound_of_convFull_adjunction
#assert_no_axioms FX1Poly.Polygraph.decidableTwoCellConvFull_of_adjunction

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcGodementSoundnessViaPeel
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcGodementSoundnessPeelEmptyBoundary

end FX1PolyAudit
