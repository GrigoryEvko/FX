import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingLastCupShortChord

/-! # FX1PolyAudit/…/MatchingLastCupShortChord — zero-axiom gate

Per-declaration zero-axiom gate for the width-`0` LOCATE port (Track B route 1, brick 1): the
last cup of a boundary-chained pure-cup spine over the width-`0` bottom boundary reads off
`matchingOfSpineList 0`'s partner as a short chord, ported to the plain `WireState` union-find
positivity-free (no `0 < bottomCount`, no `nfPos`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepCupMatching_forwardPartner
#assert_no_axioms FX1Poly.Polygraph.wireStateFresh_processSpine_ofAllCup
#assert_no_axioms FX1Poly.Polygraph.processSpine_openWires_length_ofChainedAppend
#assert_no_axioms FX1Poly.Polygraph.processSpine_prefix_openWires_eq_lastDomBoundary
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_prefix_ofAppend'
#assert_no_axioms FX1Poly.Polygraph.matchingLastCup_isShortChord
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingLastCupShortChord

end FX1PolyAudit
