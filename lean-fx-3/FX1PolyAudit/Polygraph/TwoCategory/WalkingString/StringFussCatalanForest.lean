import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanForest

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalanForest — zero-axiom gate (FC-3b, residual (i))

Per-declaration zero-axiom gate for the union-find FOREST invariant + the FUEL NORMALIZATION: the forest predicate
and its chain (`stringIsUnionFindForest`, `_nil`, the settling lemma, JOIN + fold preservation), the fuel-split /
fuel-bump, and the composite fresh-edge below-bound `isSameComponent` invariance.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringIsUnionFindForest
#assert_no_axioms FX1Poly.Polygraph.stringIsUnionFindForest_nil
#assert_no_axioms FX1Poly.Polygraph.stringUnionFindRoot_consJoin
#assert_no_axioms FX1Poly.Polygraph.stringUnionFindRootOf_parentless_of_forest
#assert_no_axioms FX1Poly.Polygraph.stringUnionFindForest_unionFindJoin
#assert_no_axioms FX1Poly.Polygraph.stringUnionFindForest_stepCup
#assert_no_axioms FX1Poly.Polygraph.stringUnionFindForest_stepCap
#assert_no_axioms FX1Poly.Polygraph.stringUnionFindForest_stepAtom
#assert_no_axioms FX1Poly.Polygraph.stringUnionFindForest_processSpine
#assert_no_axioms FX1Poly.Polygraph.stringInitialWireState_isUnionFindForest
#assert_no_axioms FX1Poly.Polygraph.stringProcessSpine_isUnionFindForest_fromSeed
#assert_no_axioms FX1Poly.Polygraph.stringUnionFindRoot_fuelSplit
#assert_no_axioms FX1Poly.Polygraph.stringUnionFindRoot_fuelBump_of_forest
#assert_no_axioms FX1Poly.Polygraph.stringUnionFindRootOf_cons_freshAbove_forest
#assert_no_axioms FX1Poly.Polygraph.stringIsSameComponent_cons_freshAbove_forest
#assert_no_axioms FX1Poly.Polygraph.fxString_hasForestFuelNormalization

end FX1PolyAudit
