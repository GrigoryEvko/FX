import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupTouchingIrreducible

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCupTouchingIrreducibleAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the BRAUER cup-touching-crossing
irreducibility wall — the two leg-adjacent straddle relocators, the diagram-inequality irreducibility pins at b=3 and b=4,
the straddle⇄crossingLeft orbit pin, the stuck-residue crossing count, the multi-step driveCanonical bundle and its untwist
(canonical) and straddle (jammed) exemplars, the same-descent-different-fate pin, the honesty marker, and the machine-checked
terminal state.  Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.straddlePlusSlide_clean
#print axioms FX1Poly.Polygraph.crossingLeftSlide_clean
#print axioms FX1Poly.Polygraph.cupTouchingCrossing_notBareCup_b3
#print axioms FX1Poly.Polygraph.cupTouchingCrossing_notBareCup_b4
#print axioms FX1Poly.Polygraph.straddleCrossingLeft_shareDiagram
#print axioms FX1Poly.Polygraph.residueIrreducibleCrossingCount
#print axioms FX1Poly.Polygraph.MultiStepDrive
#print axioms FX1Poly.Polygraph.driveUntwistExemplar
#print axioms FX1Poly.Polygraph.driveUntwistExemplar_targetArrived
#print axioms FX1Poly.Polygraph.driveStraddleExemplar
#print axioms FX1Poly.Polygraph.driveStraddleExemplar_jams
#print axioms FX1Poly.Polygraph.driveFates_descendSame_landDifferent
#print axioms FX1Poly.Polygraph.fxBrauer_hasCupTouchingIrreducibility
#print axioms FX1Poly.Polygraph.fxBrauer_cupTouchingIrreducibleTerminalState

end FX1PolyAudit
