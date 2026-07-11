import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingFoldAlignment

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCrossingFoldAlignment — zero-axiom gate (BRAUER r17/r18 E3)

Per-declaration zero-axiom gate for the E3 opening: the fold-alignment target invariant
(`foldRealizesTargetDiagram`, TRUE on adversarial-B), the crossing-staircase width invariant
(`crossingWordFold_openWires_length`, with its concrete probe), the r18 crossing-phase connectivity correspondence
(`crossingWord_openWire_sameComponent_bottomPort` — the E3 wall's exact stated goal, from the shipped `boundView`),
and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the E3 / T-CLOSE(b) target invariant + its adversarial-B inhabitant
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagram
#assert_no_axioms FX1Poly.Polygraph.foldRealizesTargetDiagram_adversarialB

-- the first structural alignment brick (the crossing staircase preserves the open-wire count) + its probe
#assert_no_axioms FX1Poly.Polygraph.crossingWordFold_openWires_length
#assert_no_axioms FX1Poly.Polygraph.crossingWordFold_openWires_length_probe

-- (r18) the E3 crossing-phase connectivity correspondence (the wall's exact stated goal, from the shipped boundView)
#assert_no_axioms FX1Poly.Polygraph.stateIsPermGraph_openWire_sameComponent_bottomPort
#assert_no_axioms FX1Poly.Polygraph.crossingWord_openWire_sameComponent_bottomPort
#assert_no_axioms FX1Poly.Polygraph.crossingWord_openWire_sameComponent_bottomPort_probe

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingFoldWidthInvariant
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingStaircaseConnectivity
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFoldAlignmentE3

end FX1PolyAudit
