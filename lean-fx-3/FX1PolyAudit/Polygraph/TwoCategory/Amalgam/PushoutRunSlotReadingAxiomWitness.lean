import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutRunSlotReading

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutRunSlotReadingAxiomWitness — independent #print axioms (WP-AMALG)

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the
wall-free gap-slot substrate brick.  Each must print "does not depend on any axioms".
Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Amalgam.GapSlot
#print axioms FX1Poly.Polygraph.Amalgam.interleaveRuns
#print axioms FX1Poly.Polygraph.Amalgam.flatSlotsDom
#print axioms FX1Poly.Polygraph.Amalgam.flatSlotsCod
#print axioms FX1Poly.Polygraph.Amalgam.flatSlotsCell
#print axioms FX1Poly.Polygraph.Amalgam.tRunWord
#print axioms FX1Poly.Polygraph.Amalgam.runsWord
#print axioms FX1Poly.Polygraph.Amalgam.wallFreeLetter_eq_tLetter
#print axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_wallFree
#print axioms FX1Poly.Polygraph.Amalgam.wallFreeRun_eq_of_length
#print axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_composePathHom
#print axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_flatDom
#print axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_flatCod
#print axioms FX1Poly.Polygraph.Amalgam.sLetter_ne_tLetter
#print axioms FX1Poly.Polygraph.Amalgam.runsWord_zero_nil
#print axioms FX1Poly.Polygraph.Amalgam.runsWord_zero_cons
#print axioms FX1Poly.Polygraph.Amalgam.runsWord_succPeel
#print axioms FX1Poly.Polygraph.Amalgam.runsWord_parse_unique
#print axioms FX1Poly.Polygraph.Amalgam.slotRuns_aligned_of_lengths
#print axioms FX1Poly.Polygraph.Amalgam.flatBoundary_slots_aligned
#print axioms FX1Poly.Polygraph.Amalgam.segmentRuns
#print axioms FX1Poly.Polygraph.Amalgam.AllRunsWallFree
#print axioms FX1Poly.Polygraph.Amalgam.segmentRuns_allWallFree
#print axioms FX1Poly.Polygraph.Amalgam.runsWord_segmentRuns
#print axioms FX1Poly.Polygraph.Amalgam.pushoutPathWord_interleaveRuns
#print axioms FX1Poly.Polygraph.Amalgam.interleave_segmentRuns
#print axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasRunSlotSubstrate

end FX1PolyAudit
