import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectCapChain

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescTConnectCapChain — zero-axiom gate (BRAUER r24, the CAP chain:
the GENERAL per-arc CAP-class T-CONNECT assembled)

Per-declaration zero-axiom gate for the cap-chain assembly: the propext-free position-bookkeeping kit
(`doublePos_add`, `chunkFrontPairs_flatten_split`, `chunkFrontPairs_length`, `flattenNatPairs_pairGetMem`,
`expandBottomFeetPairs_getAt_fst` / `_snd`, `natListGetAtAppendLeftCap`, `natListGetAtMemCap`), the six-phase
factorization (`foldFactorsThroughCap`), the abstract-state cap chain (`capArcConnectViaState`), the GENERAL per-arc
CAP-class T-CONNECT (`capArcConnect_general`) and its boundary-matching lift (`capArcMatching_general`), the concrete
decode + join probes, and the ingredient marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.doublePos_add
#assert_no_axioms FX1Poly.Polygraph.doublePos_lt_doublePos
#assert_no_axioms FX1Poly.Polygraph.doublePos_succ_lt_doublePos
#assert_no_axioms FX1Poly.Polygraph.chunkFrontPairs_flatten_split
#assert_no_axioms FX1Poly.Polygraph.chunkFrontPairs_length
#assert_no_axioms FX1Poly.Polygraph.flattenNatPairs_length_doublePos
#assert_no_axioms FX1Poly.Polygraph.flattenNatPairs_pairGetMem
#assert_no_axioms FX1Poly.Polygraph.expandBottomFeetPairs_getAt_fst
#assert_no_axioms FX1Poly.Polygraph.expandBottomFeetPairs_getAt_snd
#assert_no_axioms FX1Poly.Polygraph.natListGetAtAppendLeftCap
#assert_no_axioms FX1Poly.Polygraph.natListGetAtMemCap
#assert_no_axioms FX1Poly.Polygraph.foldFactorsThroughCap
#assert_no_axioms FX1Poly.Polygraph.capArcConnectViaState
#assert_no_axioms FX1Poly.Polygraph.capArcConnect_general
#assert_no_axioms FX1Poly.Polygraph.capArcMatching_general
#assert_no_axioms FX1Poly.Polygraph.capChainDecodeProbe_allCaps
#assert_no_axioms FX1Poly.Polygraph.capChainJoinProbe_allCaps
#assert_no_axioms FX1Poly.Polygraph.capArcConnect_firesAllCaps_zero
#assert_no_axioms FX1Poly.Polygraph.capArcMatching_firesAllCaps_one
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasTConnectCapClass

end FX1PolyAudit
