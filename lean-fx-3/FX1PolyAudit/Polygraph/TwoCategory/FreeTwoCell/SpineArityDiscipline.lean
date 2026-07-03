import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineArityDiscipline

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SpineArityDiscipline — zero-axiom gate

Per-declaration zero-axiom gate for the arity-discipline + state-tracking kit: the list-level
cup/cap discipline with cons manipulation, production/extraction across spine difference-lists,
Godement-step and trace-equivalence invariance, the cell-level seed, the per-atom state
tracking bridge, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SpineHasCupCapAtoms
#assert_no_axioms FX1Poly.Polygraph.spineHasCupCapAtoms_tail
#assert_no_axioms FX1Poly.Polygraph.spineHasCupCapAtoms_cons
#assert_no_axioms FX1Poly.Polygraph.spineHasCupCapAtoms_spineDiff
#assert_no_axioms FX1Poly.Polygraph.cellCupCap_and_restAtoms_of_spineDiff
#assert_no_axioms FX1Poly.Polygraph.SpineGodementStep.cupCapAtomsIff
#assert_no_axioms FX1Poly.Polygraph.SpineTraceEquiv.cupCapAtomsIff
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spineHasCupCapAtoms_spine
#assert_no_axioms FX1Poly.Polygraph.stepAtom_openWires_tracksBoundary
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineArityDisciplineKit

end FX1PolyAudit
