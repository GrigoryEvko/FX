import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescExt5CorrectedRoundtripBridge

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescExt5CorrectedRoundtripBridge — zero-axiom gate (r54)

Per-declaration zero-axiom gate for the BRAUER r54 R3-A roundtrip bridge (the FIRST TRANCHE): the marker-bridge
(`ext5CorrectedRoundtrip_ofPos`), the census bridge (`isBoundaryInvolution_ofValidCensus`) and its payoff
(`ext5CorrectedRoundtrip_ofValidCensus`), the tranche fired on the entangled / with-cap witnesses
(`ext5CorrectedRoundtrip_monster`, `_monster_viaCensus`, `_adversarialB`, `_wildCapThrough`, `_wildCrossThrough`), the
`bottomCount = 0` residual pins (`nestedCups_bottomCount_zero`, `ext5CorrectedRoundtrip_nestedCups_decide`), the content
marker, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `WellFounded.fix`.  The
bridges compose the shipped `extractDiagram_correctedWord_general` with structural propext-free micro-helpers over
`List.all` / `List.range` / `Nat.beq` / `Nat.blt`; the witness firings supply `0 < bottomCount` / `isInvolutionPartner`
premises by `decide`; the residual pin is a `decide` on a small concrete diagram equality.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_ofPos
#assert_no_axioms FX1Poly.Polygraph.isBoundaryInvolution_ofValidCensus
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_ofValidCensus
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_monster
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_monster_viaCensus
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_adversarialB
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_wildCapThrough
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_wildCrossThrough
#assert_no_axioms FX1Poly.Polygraph.nestedCups_bottomCount_zero
#assert_no_axioms FX1Poly.Polygraph.ext5CorrectedRoundtrip_nestedCups_decide
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasExt5CorrectedRoundtripPosBottom
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_ext5CorrectedRoundtripBridgeTerminalState

end FX1PolyAudit
