import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingBoundaryDiscipline

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingBoundaryDiscipline — zero-axiom gate

Per-declaration zero-axiom gate for the boundary-disciplined soundness: the instance-level
in-range extract commutation, the enriched trace induction, the re-seated soundness capstone,
and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingGodementCommute_ofInRange
#assert_no_axioms FX1Poly.Polygraph.traceInvariant_of_boundaryDiscipline
#assert_no_axioms FX1Poly.Polygraph.matchingOf_sound_ofCupCapCells
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasBoundaryDisciplinedSoundness

end FX1PolyAudit
