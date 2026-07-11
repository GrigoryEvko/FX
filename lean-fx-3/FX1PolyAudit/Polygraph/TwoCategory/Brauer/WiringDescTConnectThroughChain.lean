import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectThroughChain

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescTConnectThroughChain — zero-axiom gate (BRAUER r26, the THROUGH
width-12 monster probe + honest 5-phase scope)

Per-declaration zero-axiom gate for the THROUGH monster probe: the boundary-involution witness
(`monster_isBoundaryInvolution`), the width-12 arc / non-arc probes (`monsterWidth12Arcs`, `monsterWidth12NonArcs`),
the r27 P1 seam decode read-off (`throughReadOffBottom_reads_throughFoot` + its monster / 3-through firings, which
consume the r27 ROUNDTRIP CRUX), and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.monster_isBoundaryInvolution
#assert_no_axioms FX1Poly.Polygraph.monsterWidth12Arcs
#assert_no_axioms FX1Poly.Polygraph.monsterWidth12NonArcs
#assert_no_axioms FX1Poly.Polygraph.throughReadOffBottom_reads_throughFoot
#assert_no_axioms FX1Poly.Polygraph.throughReadOffBottom_reads_throughFoot_firesMonster
#assert_no_axioms FX1Poly.Polygraph.throughReadOffBottom_reads_throughFoot_fires3Through
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasThroughWidth12Probe
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasThroughReadOffFoot
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasThroughClassGeneral

end FX1PolyAudit
