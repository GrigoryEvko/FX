import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPadCongruence

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescPadCongruence — zero-axiom gate (KEYSTONE15)

Per-declaration zero-axiom gate for the horizontal RIGHT-pad congruence port from the walking-adjunction spine to
the Brauer engine: the block-many list surgery left of a constant suffix, the fresh-block re-basing under the shift,
the node-wise renamed endpoint / arc trace, `freshShiftAbove` injectivity, the pad-zone inertness of an all-avoiding
event fold, the light right-pad wire simulation with its step / fold / whole-word trace correspondence, the whole-word
right-pad simulation `processBrauer_rightPadSim`, and the payoff `brauerSeedExtract_ofRightPad`.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- list surgery + fresh-block re-basing
#assert_no_axioms FX1Poly.Polygraph.natListRemoveManyAt_append_left
#assert_no_axioms FX1Poly.Polygraph.natListSliceAt_append_left
#assert_no_axioms FX1Poly.Polygraph.rightPadOutputNodes_map

-- node-wise renamed endpoint / arc trace
#assert_no_axioms FX1Poly.Polygraph.wiringEndpointNode_mapNodes
#assert_no_axioms FX1Poly.Polygraph.wiringArcEvents_mapNodes

-- shift injectivity + pad-zone inertness
#assert_no_axioms FX1Poly.Polygraph.freshShiftAbove_injective
#assert_no_axioms FX1Poly.Polygraph.renamedTraceAvoidsPadZone
#assert_no_axioms FX1Poly.Polygraph.applyJoinEvents_padInert

-- the light wire simulation, step, fold, trace correspondence
#assert_no_axioms FX1Poly.Polygraph.RightPadWireSim
#assert_no_axioms FX1Poly.Polygraph.stepWiring_rightPadWireSim
#assert_no_axioms FX1Poly.Polygraph.processBrauer_rightPadWireSim
#assert_no_axioms FX1Poly.Polygraph.rightPadWireSim_wordJoinEvents

-- the whole-word right-pad simulation + payoff
#assert_no_axioms FX1Poly.Polygraph.processBrauer_rightPadSim
#assert_no_axioms FX1Poly.Polygraph.brauerSeedExtract_ofRightPad

-- the LEFT pad: shifted word + prefix-skip surgery + simulation + payoff
#assert_no_axioms FX1Poly.Polygraph.shiftBrauerWord
#assert_no_axioms FX1Poly.Polygraph.shiftBrauerWord_internalLoops
#assert_no_axioms FX1Poly.Polygraph.brauerWordInRange_shift
#assert_no_axioms FX1Poly.Polygraph.brauerWordInRange_rightExtend
#assert_no_axioms FX1Poly.Polygraph.LeftPadWireSim
#assert_no_axioms FX1Poly.Polygraph.stepWiring_leftPadWireSim
#assert_no_axioms FX1Poly.Polygraph.processBrauer_leftPadWireSim
#assert_no_axioms FX1Poly.Polygraph.leftPadWireSim_wordJoinEvents
#assert_no_axioms FX1Poly.Polygraph.processBrauer_leftPadSim
#assert_no_axioms FX1Poly.Polygraph.brauerSeedExtract_ofLeftPad

-- the two-sided composition + the 5 relations in arbitrary horizontal context
#assert_no_axioms FX1Poly.Polygraph.brauerSeedExtract_ofTwoSidedPad
#assert_no_axioms FX1Poly.Polygraph.brauerConv_relation_inContext
#assert_no_axioms FX1Poly.Polygraph.brauerConv_crossingInvolution_inWiderContext
#assert_no_axioms FX1Poly.Polygraph.brauerConv_yangBaxter_inWiderContext
#assert_no_axioms FX1Poly.Polygraph.brauerConv_capSlide_inWiderContext
#assert_no_axioms FX1Poly.Polygraph.brauerConv_snake_inWiderContext
#assert_no_axioms FX1Poly.Polygraph.brauerConv_snakeMirror_inWiderContext

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasRightPadCongruence
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasTwoSidedPadCongruence
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasRelationInArbitraryHorizontalContext

-- the flipped soundness flag (now `true`) + updated residual markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerSoundness
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerSoundnessResidualIsPadShift
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerSoundnessResidualNamed

end FX1PolyAudit
