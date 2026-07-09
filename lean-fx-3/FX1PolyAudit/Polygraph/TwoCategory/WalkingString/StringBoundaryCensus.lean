import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringBoundaryCensus

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringBoundaryCensus — zero-axiom gate (FC-5, P1)

Per-declaration zero-axiom gate for the two-endpoint boundary census over the bare `WireState`: the forest bridge,
the seed leg, the cup / cap step preservation, and the fold transport.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringForest_toUnionFindForest
#assert_no_axioms FX1Poly.Polygraph.stringBoundaryCensus_initial
#assert_no_axioms FX1Poly.Polygraph.stringCapEndTokenBackmap_node
#assert_no_axioms FX1Poly.Polygraph.stringCapEndTokenBackmap_isValid
#assert_no_axioms FX1Poly.Polygraph.stringBoundaryCensus_stepCap
#assert_no_axioms FX1Poly.Polygraph.stringCupEndTokenBackmap_node
#assert_no_axioms FX1Poly.Polygraph.stringCupEndTokenBackmap_isValid
#assert_no_axioms FX1Poly.Polygraph.stringStepCup_links_cons
#assert_no_axioms FX1Poly.Polygraph.stringNotSame_of_rootsNe
#assert_no_axioms FX1Poly.Polygraph.stringCupLegSeparation
#assert_no_axioms FX1Poly.Polygraph.stringBoundaryCensus_stepCup
#assert_no_axioms FX1Poly.Polygraph.StringWireStateFresh_stepAtom
#assert_no_axioms FX1Poly.Polygraph.stringBoundaryCensus_stepAtom
#assert_no_axioms FX1Poly.Polygraph.stringBoundaryCensus_processSpine_ofChained
#assert_no_axioms FX1Poly.Polygraph.stringBoundaryCensus_fromCell
#assert_no_axioms FX1Poly.Polygraph.fxString_hasBoundaryCensus
#assert_no_axioms FX1Poly.Polygraph.fxString_hasBoundaryCensusUnlocksBothResiduals

end FX1PolyAudit
