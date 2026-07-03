import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryGodement

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SpineBoundaryGodement — zero-axiom gate

Per-declaration zero-axiom gate for the Godement-nest boundary kit: the cross-layer boundary
conversion, the entry dichotomies for both interchange nests, peel/build between pinned entry
and common exit, step preservation/reflection of boundary chains, full trace-equivalence
invariance, the in-range window bound, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.crossLayerBoundaryEq
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_interchangeRedex_entryPinned
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_interchangeReduct_entryPinned
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_interchangeRedex_exit
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_interchangeRedex_ofExit
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_interchangeReduct_exit
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_interchangeReduct_ofExit
#assert_no_axioms FX1Poly.Polygraph.SpineGodementStep.preservesBoundaryChained
#assert_no_axioms FX1Poly.Polygraph.SpineGodementStep.reflectsBoundaryChained
#assert_no_axioms FX1Poly.Polygraph.SpineTraceEquiv.boundaryChainedIff
#assert_no_axioms FX1Poly.Polygraph.interchangeWindow_le_ofEntryPinned
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineBoundaryGodementKit

end FX1PolyAudit
