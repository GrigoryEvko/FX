import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanFreshness

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalanFreshness — zero-axiom gate (FC-3 A-i)

Per-declaration zero-axiom gate for the union-find FRESHNESS core: the parent facts (`cons_ofChildNe`,
`none_of_notChild`, `some_mem_snd`), the fresh-node root facts (`of_parentNone`, `of_notChild`), the substantive
below-bound root-preservation lemma (`unionFindRoot_cons_freshAbove`), and the freshness invariant + fresh seed.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.unionFindParent_cons_ofChildNe
#assert_no_axioms FX1Poly.Polygraph.unionFindParent_none_of_notChild
#assert_no_axioms FX1Poly.Polygraph.unionFindParent_some_mem_snd
#assert_no_axioms FX1Poly.Polygraph.unionFindRoot_of_parentNone
#assert_no_axioms FX1Poly.Polygraph.unionFindRootOf_of_notChild
#assert_no_axioms FX1Poly.Polygraph.unionFindRoot_cons_freshAbove
#assert_no_axioms FX1Poly.Polygraph.StringWireStateFresh
#assert_no_axioms FX1Poly.Polygraph.StringWireStateFresh_parentsBelow
#assert_no_axioms FX1Poly.Polygraph.stringInitialWireState_fresh
#assert_no_axioms FX1Poly.Polygraph.natListInsertAt_mem
#assert_no_axioms FX1Poly.Polygraph.unionFindJoin_freshPair
#assert_no_axioms FX1Poly.Polygraph.StringWireStateFresh_stepCup
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCupFreshnessKit
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCupPreservationFromFreshness

end FX1PolyAudit
