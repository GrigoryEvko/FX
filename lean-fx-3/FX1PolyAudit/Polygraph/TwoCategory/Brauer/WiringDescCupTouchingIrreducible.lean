import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupTouchingIrreducible

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCupTouchingIrreducible — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER cup-touching-crossing irreducibility wall (the SIXTH honest zero-flip): the
two leg-adjacent straddle relocators over the shipped cup slide (`straddlePlusSlide_clean`, `crossingLeftSlide_clean`), the
LOAD-BEARING diagram-inequality irreducibility pins at b=3 and b=4 (`cupTouchingCrossing_notBareCup_b3`/`_b4`), the
straddle⇄crossingLeft orbit pin (`straddleCrossingLeft_shareDiagram`), the stuck-residue crossing count
(`residueIrreducibleCrossingCount`), the multi-step driveCanonical bundle (`MultiStepDrive`) with the untwist arm
canonicalising to a bare cup (`driveUntwistExemplar`, `driveUntwistExemplar_targetArrived`) and the straddle arm jamming at a
cup-touching crossing (`driveStraddleExemplar`, `driveStraddleExemplar_jams`), the same-descent-different-fate pin
(`driveFates_descendSame_landDifferent`), the honesty marker, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the descents are `crossingCount`
`decide`s over `Nat.decLt`, the irreducibility is a `brauerDiagramOf` INEQUALITY via the derived `DecidableEq` on
`DiagramType` (the b=3 pin through `Nat.decidableBallLT`), and the drives compose the shipped `straddleSlideFree8_clean` /
`cupUntwistFree8_clean` / `crossingCancelFree` by `trans` / `whiskerLeft` / `whiskerRight` (no opaque transport, no
`WellFounded.fix` / `termination_by`).  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.straddlePlusSlide_clean
#assert_no_axioms FX1Poly.Polygraph.crossingLeftSlide_clean
#assert_no_axioms FX1Poly.Polygraph.cupTouchingCrossing_notBareCup_b3
#assert_no_axioms FX1Poly.Polygraph.cupTouchingCrossing_notBareCup_b4
#assert_no_axioms FX1Poly.Polygraph.straddleCrossingLeft_shareDiagram
#assert_no_axioms FX1Poly.Polygraph.residueIrreducibleCrossingCount
#assert_no_axioms FX1Poly.Polygraph.MultiStepDrive
#assert_no_axioms FX1Poly.Polygraph.driveUntwistExemplar
#assert_no_axioms FX1Poly.Polygraph.driveUntwistExemplar_targetArrived
#assert_no_axioms FX1Poly.Polygraph.driveStraddleExemplar
#assert_no_axioms FX1Poly.Polygraph.driveStraddleExemplar_jams
#assert_no_axioms FX1Poly.Polygraph.driveFates_descendSame_landDifferent
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCupTouchingIrreducibility
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_cupTouchingIrreducibleTerminalState

end FX1PolyAudit
