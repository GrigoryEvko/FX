import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringBoundaryCensus

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringBoundaryCensus — zero-axiom gate (FC-5, P1)

Per-declaration zero-axiom gate for the two-endpoint boundary census over the bare `WireState`: the forest bridge,
the seed leg, the cup / cap step preservation, and the fold transport.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringForest_toUnionFindForest
#assert_no_axioms FX1Poly.Polygraph.stringBoundaryCensus_initial

end FX1PolyAudit
