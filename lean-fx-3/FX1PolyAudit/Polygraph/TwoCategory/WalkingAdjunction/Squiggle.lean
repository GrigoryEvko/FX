import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.Squiggle

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.Squiggle — zero-axiom gate (SQ-1)

Per-declaration zero-axiom gate for the ORIENTED squiggle normal-form carrier (RV Def 3.1.2): the port
orientation `PortSide` and its decider `portSideDecEq`, the oriented letter `SquiggleLetter` with its
hand-rolled `squiggleLetterDecEq`, the string-level decider `squiggleStringDecEq`, the decidable
strict-undulation well-formedness (`isStrictlyUndulatingFrom`, `isStrictlyUndulating`), the smoke facts,
and the two honesty markers (`fxMode_hasOrientedSquiggleCarrier := true`,
`fxMode_hasOrientedSquiggleFoldSoundness := false`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.portSideDecEq
#assert_no_axioms FX1Poly.Polygraph.squiggleLetterDecEq
#assert_no_axioms FX1Poly.Polygraph.squiggleStringDecEq
#assert_no_axioms FX1Poly.Polygraph.isStrictlyUndulatingFrom
#assert_no_axioms FX1Poly.Polygraph.isStrictlyUndulating
#assert_no_axioms FX1Poly.Polygraph.isStrictlyUndulating_zigzag
#assert_no_axioms FX1Poly.Polygraph.not_isStrictlyUndulating_staircase
#assert_no_axioms FX1Poly.Polygraph.not_isStrictlyUndulating_jump
#assert_no_axioms FX1Poly.Polygraph.squiggleLetter_side_discriminated
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasOrientedSquiggleCarrier
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasOrientedSquiggleFoldSoundness

end FX1PolyAudit
