import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadWindowUniversalRefuted

/-! # FX1PolyAudit/…/ArcCupHeadWindowUniversalRefuted — zero-axiom gate

Per-declaration zero-axiom gate for the R1c refutation: two boundary-chained, cup-headed spines at boundary
`2` whose head cups differ only in window (`0` vs `2`) share the WHOLE `FullArcStructure` (diagram, totals,
AND `internalCupCounts`), realized by genuine parallel cells — so the universal head-cup window readoff is
FALSE and the head window is genuine trace-orbit content, not an arc-field readoff.  Every declaration must
be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.orbitSpineHeadFront_isChained
#assert_no_axioms FX1Poly.Polygraph.orbitSpineHeadBack_isChained
#assert_no_axioms FX1Poly.Polygraph.orbitSpineHeadFront_atomReadoff
#assert_no_axioms FX1Poly.Polygraph.orbitSpineHeadBack_atomReadoff
#assert_no_axioms FX1Poly.Polygraph.orbitSpines_arcStructure_eq
#assert_no_axioms FX1Poly.Polygraph.orbitSpineHeadFront_headIsCup
#assert_no_axioms FX1Poly.Polygraph.orbitSpineHeadBack_headIsCup
#assert_no_axioms FX1Poly.Polygraph.orbitSpines_headWindows_ne
#assert_no_axioms FX1Poly.Polygraph.headCupWindowReadoff_isFalse
#assert_no_axioms FX1Poly.Polygraph.orbitCellHeadFront_spine
#assert_no_axioms FX1Poly.Polygraph.orbitCellHeadBack_spine
#assert_no_axioms FX1Poly.Polygraph.orbitCells_arcStructure_eq
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupHeadWindowUniversalRefuted

end FX1PolyAudit
