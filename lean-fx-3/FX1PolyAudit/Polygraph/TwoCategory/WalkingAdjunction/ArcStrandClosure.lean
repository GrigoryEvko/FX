import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStrandClosure

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcStrandClosure — zero-axiom gate

Per-declaration zero-axiom gate for the closed-strand substrate (peel campaign H,
strand-closure rung 1): the avoided-join workhorse, the `ArcStrandClosure` invariant, and the
per-step query-stability computations.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_ofAvoided
#assert_no_axioms FX1Poly.Polygraph.ArcStrandClosure
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCupArc_queriesStable
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCapArc_queriesStable

end FX1PolyAudit
