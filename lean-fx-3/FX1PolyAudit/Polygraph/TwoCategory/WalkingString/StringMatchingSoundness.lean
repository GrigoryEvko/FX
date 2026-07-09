import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingSoundness

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringMatchingSoundness — zero-axiom gate

Per-declaration zero-axiom gate for the unconditional two-level soundness: the boundary-disciplined soundness
(the `ofFull` cross-colour Godement leg discharged by the cup/cap capstone), the unconditional base and coloured
soundness, the two non-vacuity witnesses (the two `G`-snakes identified, the cross-level cell distinguished from
`id_G`), and the two markers (the no-obstruction wall record and the discharge marker).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringSaturatedConv_matchingOf_eq_ofBoundaryDiscipline
#assert_no_axioms FX1Poly.Polygraph.stringSaturatedConv_matchingOf_eq_final
#assert_no_axioms FX1Poly.Polygraph.stringSaturatedConv_colouredMatchingOf_eq_final
#assert_no_axioms FX1Poly.Polygraph.stringSnakeGlo_colouredMatchingOf_eq_stringSnakeGhi
#assert_no_axioms FX1Poly.Polygraph.stringCrossLevel_colouredMatchingOf_ne_identityG
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCrossColourGodementObstruction
#assert_no_axioms FX1Poly.Polygraph.fxString_hasAdjointTripleSoundnessDischarged

end FX1PolyAudit
