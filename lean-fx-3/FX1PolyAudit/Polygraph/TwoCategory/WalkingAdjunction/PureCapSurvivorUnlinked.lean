import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.PureCapSurvivorUnlinked

/-! # FX1PolyAudit/…/PureCapSurvivorUnlinked — zero-axiom gate

Per-declaration zero-axiom gate for brick (2a) of the pure-cap survivor readoff: every surviving
open wire of a pure-cap block run from the canonical seed is `ArcNodeUnlinked`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.mem_imp_getAt
#assert_no_axioms FX1Poly.Polygraph.distinctReadNe
#assert_no_axioms FX1Poly.Polygraph.ne_reads_of_mem_natListRemoveTwoAt
#assert_no_axioms FX1Poly.Polygraph.stepCap_allUnlinked
#assert_no_axioms FX1Poly.Polygraph.processSpine_allUnlinked_ofAllCapArity
#assert_no_axioms FX1Poly.Polygraph.processSpine_openWires_unlinked_ofAllCapArity_seed
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasPureCapSurvivorUnlinked

end FX1PolyAudit
