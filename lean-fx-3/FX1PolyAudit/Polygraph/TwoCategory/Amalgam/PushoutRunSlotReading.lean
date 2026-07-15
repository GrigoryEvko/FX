import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutRunSlotReading

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutRunSlotReading — zero-axiom gate (WP-AMALG)

Per-declaration zero-axiom gate for the wall-free gap-slot substrate: the slot + flat layout,
the word coordinates, parsing uniqueness, the slot alignment, and the segmentation round-trip.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.GapSlot
#assert_no_axioms FX1Poly.Polygraph.Amalgam.interleaveRuns
#assert_no_axioms FX1Poly.Polygraph.Amalgam.flatSlotsDom
#assert_no_axioms FX1Poly.Polygraph.Amalgam.flatSlotsCod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.flatSlotsCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.tRunWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.runsWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallFreeLetter_eq_tLetter
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_wallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallFreeRun_eq_of_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_composePathHom
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_flatDom
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_flatCod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.sLetter_ne_tLetter
#assert_no_axioms FX1Poly.Polygraph.Amalgam.runsWord_zero_nil
#assert_no_axioms FX1Poly.Polygraph.Amalgam.runsWord_zero_cons
#assert_no_axioms FX1Poly.Polygraph.Amalgam.runsWord_succPeel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.runsWord_parse_unique
#assert_no_axioms FX1Poly.Polygraph.Amalgam.slotRuns_aligned_of_lengths
#assert_no_axioms FX1Poly.Polygraph.Amalgam.flatBoundary_slots_aligned
#assert_no_axioms FX1Poly.Polygraph.Amalgam.segmentRuns
#assert_no_axioms FX1Poly.Polygraph.Amalgam.AllRunsWallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.segmentRuns_allWallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.runsWord_segmentRuns
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_interleaveRuns
#assert_no_axioms FX1Poly.Polygraph.Amalgam.interleave_segmentRuns
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasRunSlotSubstrate

end FX1PolyAudit
