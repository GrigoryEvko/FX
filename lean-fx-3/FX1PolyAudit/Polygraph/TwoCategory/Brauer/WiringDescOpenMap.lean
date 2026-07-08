import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescOpenMap

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescOpenMap — zero-axiom gate (KEYSTONE5)

Per-declaration zero-axiom gate for the `openMap` four-zone open-wire correspondence and the freshness-and-forest-
conditioned IN-RANGE disjoint-window interchange: the generic-width list-surgery kit (`natListRemoveManyAt_map`,
`natListRemoveManyAt_appendPrefix`, `frontRemoveMany_splice_shift`, `spliceDisjointCommute`), the `openMap` field
(`wiringDescCoreSwap_openMap`), the boundary-diagram commutation (`wiringDescCoreSwap_extract`), the in-range
interchange residual + its proof (`WiringDescDisjointWindowFreshInRange` /
`wiringDescDisjointWindowFreshInRange_proof`), the concrete-instance recovery, and the honesty markers.  The two
private helpers (`natListInsertAt_appendPrefixLocal`, `stepWiring_openWires`) are covered transitively by their
public consumers (`spliceDisjointCommute`, `wiringDescCoreSwap_openMap`) — `#assert_no_axioms` checks the full
transitive axiom set.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the generic-width list-surgery kit
#assert_no_axioms FX1Poly.Polygraph.natListRemoveManyAt_map
#assert_no_axioms FX1Poly.Polygraph.natListRemoveManyAt_appendPrefix
#assert_no_axioms FX1Poly.Polygraph.frontRemoveMany_splice_shift
#assert_no_axioms FX1Poly.Polygraph.spliceDisjointCommute

-- the openMap field + the boundary-diagram commutation
#assert_no_axioms FX1Poly.Polygraph.wiringDescCoreSwap_openMap
#assert_no_axioms FX1Poly.Polygraph.wiringDescCoreSwap_extract

-- the in-range disjoint-window interchange residual + proof + concrete instance
#assert_no_axioms FX1Poly.Polygraph.WiringDescDisjointWindowFreshInRange
#assert_no_axioms FX1Poly.Polygraph.wiringDescDisjointWindowFreshInRange_proof
#assert_no_axioms FX1Poly.Polygraph.disjointWindow_crossingCup_commute_ofGeneral

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringDescCoreSwapOpenMap
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringDescDisjointWindowFreshInRangeProof
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringDescDisjointWindowFreshResidualNamed

end FX1PolyAudit
