import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectThroughChain

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescTConnectThroughChain — zero-axiom gate (BRAUER r26, the THROUGH
width-12 monster probe + honest 5-phase scope)

Per-declaration zero-axiom gate for the THROUGH monster probe: the boundary-involution witness
(`monster_isBoundaryInvolution`), the width-12 arc / non-arc probes (`monsterWidth12Arcs`, `monsterWidth12NonArcs`),
and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.monster_isBoundaryInvolution
#assert_no_axioms FX1Poly.Polygraph.monsterWidth12Arcs
#assert_no_axioms FX1Poly.Polygraph.monsterWidth12NonArcs
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasThroughWidth12Probe
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasThroughClassGeneral

end FX1PolyAudit
