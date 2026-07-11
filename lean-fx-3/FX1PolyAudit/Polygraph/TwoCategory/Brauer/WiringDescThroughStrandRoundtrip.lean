import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescThroughStrandRoundtrip

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescThroughStrandRoundtrip — zero-axiom gate (BRAUER r27 P1 crux)

Per-declaration zero-axiom gate for the THROUGH-STRAND ROUNDTRIP CRUX: the P1 seam of the THROUGH per-arc five-phase
T-CONNECT.  `throughStrandBottoms_getAt_arcMiddleCountBelow` proves that on the strictly-ascending distinct list
`throughStrandBottoms` the count-strictly-below rank inverts `natListGetAt` — the direction-dual of the r26 rank ↔
position keystone.  Its three firing probes (monster bottoms `4`, `5`; the 3-through witness) supply the membership via
explicit `List.Mem` constructors (propext-free, NOT `decide`, which would leak `propext` / `Quot.sound` through the
`∈`-decision), and the ingredient marker.

Independent `#print axioms` (scratch) reported every declaration below as "does not depend on any axioms".  Must be
free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- the crux
#assert_no_axioms FX1Poly.Polygraph.throughStrandBottoms_getAt_arcMiddleCountBelow

-- the firing probes (propext-free membership witnesses)
#assert_no_axioms FX1Poly.Polygraph.throughStrandBottoms_getAt_arcMiddleCountBelow_firesMonster
#assert_no_axioms FX1Poly.Polygraph.throughStrandBottoms_getAt_arcMiddleCountBelow_firesMonsterHigh
#assert_no_axioms FX1Poly.Polygraph.throughStrandBottoms_getAt_arcMiddleCountBelow_fires3Through

-- the ingredient marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasThroughStrandRoundtrip

end FX1PolyAudit
