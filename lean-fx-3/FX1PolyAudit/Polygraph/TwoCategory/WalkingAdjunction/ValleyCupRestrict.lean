import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupRestrict

/-! # FX1PolyAudit/…/ValleyCupRestrict — zero-axiom gate

Per-declaration zero-axiom gate for the cup-side restriction functor `cupRestrict` (G) on `DiagramType`
(Piece II tail): the reconstruction function, the cup-run open-wire length congruence, and the three field
agreements closable without the two-run seed-relabeling bridge (`loops`, `bottomCount`, `topCount`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.processSpine_openWiresLength_congr_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.cupRestrict
#assert_no_axioms FX1Poly.Polygraph.cupRestrict_loops_eq
#assert_no_axioms FX1Poly.Polygraph.cupRestrict_bottomCount_eq
#assert_no_axioms FX1Poly.Polygraph.cupRestrict_topCount_eq
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCupRestrictDefAndCopiedFields

end FX1PolyAudit
