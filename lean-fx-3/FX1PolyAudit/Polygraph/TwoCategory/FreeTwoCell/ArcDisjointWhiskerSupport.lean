import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointWhiskerSupport

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointWhiskerSupport — zero-axiom gate (MODE-COMMUTE r23)

Per-declaration zero-axiom gate for the r23 whisker-support renaming levers (honest BRANCH (b)): the
two per-atom cup/cap renaming levers, their compound-sigma instances consuming r22's injectivity, the
identity structural base (`runArcCell_id`), the identity-corner base case consuming r22's below-base
bridge, the concrete cup-lever fire, the step-lever marker, the r23-open honesty pin, and the
refuted-keystone honesty pin.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.renameLinks_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.renameLinks_stepCapArc
#assert_no_axioms FX1Poly.Polygraph.renameLinks_compoundTransposition_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.renameLinks_compoundTransposition_stepCapArc
#assert_no_axioms FX1Poly.Polygraph.runArcCell_id
#assert_no_axioms FX1Poly.Polygraph.disjointWhiskerSupport_id_id
#assert_no_axioms FX1Poly.Polygraph.renameLinks_stepCupArc_probe
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasDisjointWhiskerStepLevers
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasDisjointWhiskerSupport
#assert_no_axioms FX1Poly.Polygraph.arcDisjointWhiskerSupport_samePartitionFresh_stays_open

end FX1PolyAudit
