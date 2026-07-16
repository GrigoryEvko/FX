import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingOperad.OperadTreeArity

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingOperad.OperadTreeArity — zero-axiom gate (the total-arity invariant + SOUNDNESS)

Per-declaration zero-axiom gate for the walking monoid operad total-arity invariant: the `arityOf` fold and its
defining / sample-tree smokes, the SOUNDNESS theorem `arityOf_congr_of_conv`, the non-vacuity witnesses (a law
fires positively; non-convertible pairs separate by arity), and the markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arityOf
#assert_no_axioms FX1Poly.Polygraph.arityOf_leaf
#assert_no_axioms FX1Poly.Polygraph.arityOf_unitOp
#assert_no_axioms FX1Poly.Polygraph.arityOf_mulOp
#assert_no_axioms FX1Poly.Polygraph.arityOf_assocLeftTree
#assert_no_axioms FX1Poly.Polygraph.arityOf_assocRightTree
#assert_no_axioms FX1Poly.Polygraph.arityOf_unitLeftTree
#assert_no_axioms FX1Poly.Polygraph.arityOf_congr_of_conv
#assert_no_axioms FX1Poly.Polygraph.operadConv_assocLeft_assocRight
#assert_no_axioms FX1Poly.Polygraph.arityOf_unitLeftTree_eq_leaf_via_soundness
#assert_no_axioms FX1Poly.Polygraph.operadNotConv_mulLeafLeaf_leaf
#assert_no_axioms FX1Poly.Polygraph.operadNotConv_unitOp_leaf
#assert_no_axioms FX1Poly.Polygraph.fxOperad_hasSignatureAndArityInvariant
#assert_no_axioms FX1Poly.Polygraph.fxOperad_hasSignatureAndAritySoundness
#assert_no_axioms FX1Poly.Polygraph.fxOperad_hasWordProblemDecided

end FX1PolyAudit
