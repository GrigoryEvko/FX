import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFunctoriality

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescFunctoriality — zero-axiom gate (KEYSTONE14)

Per-declaration zero-axiom gate for the two-word FUNCTORIALITY port from the walking-adjunction spine to the Brauer
engine: the list/discipline primitives, the relativization stack (wire sim + arc-trace rename + `_ofMidState`
read-offs), the unconditional loop reification, the reachable-state distinctness invariant discharging the zone
discipline, the headline `processBrauer_extract_eq_ofCanonicalExtractEq`, the whisker bridge, and the 5/5 functorial
non-vacuity witnesses.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- list / discipline primitives
#assert_no_axioms FX1Poly.Polygraph.natListSliceAt_map
#assert_no_axioms FX1Poly.Polygraph.natListSliceAt_length_fits
#assert_no_axioms FX1Poly.Polygraph.natListRemoveManyAt_length_fits
#assert_no_axioms FX1Poly.Polygraph.stepWiring_openWires_length_fits
#assert_no_axioms FX1Poly.Polygraph.WiringDescTagsInRange
#assert_no_axioms FX1Poly.Polygraph.BrauerWordInRange
#assert_no_axioms FX1Poly.Polygraph.brauerWordInRange_tail
#assert_no_axioms FX1Poly.Polygraph.brauerWordInternalLoops

-- the relativization stack
#assert_no_axioms FX1Poly.Polygraph.stepWiring_relativeWireSim
#assert_no_axioms FX1Poly.Polygraph.processBrauer_relativeWireSim
#assert_no_axioms FX1Poly.Polygraph.stepWiringEndpoint_ofRelativeWireSim
#assert_no_axioms FX1Poly.Polygraph.wiringArcEvents_ofRelativeWireSim
#assert_no_axioms FX1Poly.Polygraph.brauerWordJoinEvents_ofRelativeWireSim
#assert_no_axioms FX1Poly.Polygraph.processBrauer_loops_eq_addJoinEventLoops
#assert_no_axioms FX1Poly.Polygraph.processBrauer_links_ofRelativeSim
#assert_no_axioms FX1Poly.Polygraph.processBrauer_loops_ofRelativeSim
#assert_no_axioms FX1Poly.Polygraph.processBrauer_openWires_ofRelativeSim
#assert_no_axioms FX1Poly.Polygraph.processBrauer_links_ofMidState
#assert_no_axioms FX1Poly.Polygraph.processBrauer_loops_ofMidState
#assert_no_axioms FX1Poly.Polygraph.processBrauer_openWires_ofMidState

-- reachable-state distinctness invariant + zone discipline
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_removeManyAt_below
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_removeManyAt_atOrAbove
#assert_no_axioms FX1Poly.Polygraph.wireListDistinct_natListRemoveManyAt
#assert_no_axioms FX1Poly.Polygraph.stepWiring_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.processBrauer_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.brauerReachable_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.relativeWireZoneDiscipline_ofBrauerReachable

-- the headline + whisker bridge + 5/5 functorial witnesses
#assert_no_axioms FX1Poly.Polygraph.processBrauer_extract_eq_ofCanonicalExtractEq
#assert_no_axioms FX1Poly.Polygraph.brauerConv_whisker_ofCanonicalExtractEq
#assert_no_axioms FX1Poly.Polygraph.brauerConv_whisker_crossingInvolution_functorial
#assert_no_axioms FX1Poly.Polygraph.brauerConv_whisker_yangBaxter_functorial
#assert_no_axioms FX1Poly.Polygraph.brauerConv_whisker_capSlide_functorial
#assert_no_axioms FX1Poly.Polygraph.brauerConv_whisker_snake_functorial
#assert_no_axioms FX1Poly.Polygraph.brauerConv_whisker_snakeMirror_functorial

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasTwoWordFunctorialityPort
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWhiskerFromFunctoriality
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFunctorialRelationAgreesFiveOfFive
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerSoundnessResidualIsPadShift

end FX1PolyAudit
