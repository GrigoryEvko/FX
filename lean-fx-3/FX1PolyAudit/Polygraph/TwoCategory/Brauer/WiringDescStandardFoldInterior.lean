import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldInterior

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldInterior — zero-axiom gate (BRAUER-MIDDLE r5,
R3-A-INTERIOR: the interior-offset cup phase fold)

Per-declaration zero-axiom gate for the interior-offset cup phase fold: the append-at-front computation
(`natListInsertAt_zero` / `natListInsertAtFront` / `natListRemoveManyAt_zero`), the interior cup phase-atom lemma
(`stepWiring_cup_interior`), the interior cup fold (`cupFold_creates_atOffset`), its nonzero-offset non-vacuity, and
the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natListInsertAt_zero
#assert_no_axioms FX1Poly.Polygraph.natListInsertAtFront
#assert_no_axioms FX1Poly.Polygraph.natListRemoveManyAt_zero
#assert_no_axioms FX1Poly.Polygraph.stepWiring_cup_interior
#assert_no_axioms FX1Poly.Polygraph.cupFold_creates_atOffset
#assert_no_axioms FX1Poly.Polygraph.cupFold_creates_atOffset_throughOne
#assert_no_axioms FX1Poly.Polygraph.cupFold_atOffset_throughOne_diagram
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasInteriorCupFold
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasInteriorCupFoldRoundtrip

end FX1PolyAudit
