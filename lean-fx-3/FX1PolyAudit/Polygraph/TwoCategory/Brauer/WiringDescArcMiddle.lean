import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcMiddle

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcMiddle — zero-axiom gate (BRAUER-MIDDLE r1, B1)

Per-declaration zero-axiom gate for the FULL-MIDDLE readback: the permutation realizer
(`permutationToCrossingWord` + its `permutationRealizer_*` validations), the through-strand read-off
(`throughStrandPerm`, the inversion pin), the extended standard form (`standardFormWordExt` / `standardFormDiagramExt`),
the guarded readback (`standardFormOfDiagramFull`) with its unconditional soundness (`standardFormOfDiagramFull_sound`),
WALL-2 fixed (`standardFormOfDiagramFull_pureCrossing_some`), the roundtrips, WALL-1 breached at the datatype
(`straddleExt_realizes`), and the two honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.descendingSwapPositions
#assert_no_axioms FX1Poly.Polygraph.permutationRealizerFold
#assert_no_axioms FX1Poly.Polygraph.permutationToCrossingWord
#assert_no_axioms FX1Poly.Polygraph.arcMiddleCountBelow
#assert_no_axioms FX1Poly.Polygraph.throughStrandBottoms
#assert_no_axioms FX1Poly.Polygraph.throughStrandPerm
#assert_no_axioms FX1Poly.Polygraph.readCapArcPositions
#assert_no_axioms FX1Poly.Polygraph.readCupArcPositions
#assert_no_axioms FX1Poly.Polygraph.standardFormWordExt
#assert_no_axioms FX1Poly.Polygraph.standardFormDiagramExt
#assert_no_axioms FX1Poly.Polygraph.reconstructStandardFormFull
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramFull
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramFull_sound
#assert_no_axioms FX1Poly.Polygraph.permutationRealizer_transposition
#assert_no_axioms FX1Poly.Polygraph.permutationRealizer_threeCycle
#assert_no_axioms FX1Poly.Polygraph.permutationRealizer_reversal
#assert_no_axioms FX1Poly.Polygraph.permutationRealizer_identity
#assert_no_axioms FX1Poly.Polygraph.permutationRealizer_width4
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramFull_pureCrossing_some
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramFull_roundtrip_identity
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramFull_roundtrip_cupCap
#assert_no_axioms FX1Poly.Polygraph.straddleExt_realizes
#assert_no_axioms FX1Poly.Polygraph.straddleExt_realizes_word
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramFull_straddle_none
#assert_no_axioms FX1Poly.Polygraph.standardFormOfDiagramFull_nonVacuity
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFullMiddleReadback
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingCupArcExtractor

end FX1PolyAudit
