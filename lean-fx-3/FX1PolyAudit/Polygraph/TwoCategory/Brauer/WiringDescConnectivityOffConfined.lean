import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescConnectivityOffConfined

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescConnectivityOffConfined — zero-axiom gate (KEYSTONE10 ingredient)

Per-declaration zero-axiom gate for the off-support (CONVERSE) half of the same-component locality lifted to WORD
granularity: the single-step engine converse (`stepWiring_isSameComponent_offConfined`), the whole-word link
reification (`processBrauer_links_eq_applyJoinEvents`), the whole-word converse
(`processBrauer_isSameComponent_offConfined`), and the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepWiring_isSameComponent_offConfined
#assert_no_axioms FX1Poly.Polygraph.processBrauer_links_eq_applyJoinEvents
#assert_no_axioms FX1Poly.Polygraph.processBrauer_isSameComponent_offConfined

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasOffConfinedConverseAtWord

end FX1PolyAudit
