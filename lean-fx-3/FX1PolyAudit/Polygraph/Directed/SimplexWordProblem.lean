import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Directed.SimplexWordProblem

/-! # FX1PolyAudit/Polygraph/Directed/SimplexWordProblem — zero-axiom gate
    (the simplex-category Δ word problem, monotone-map model)

Per-declaration zero-axiom gate for the simplex-category word problem: the non-dependent `MonoMap` model, the
structural well-formedness kit (`sdwLength` / `sdwEntriesBelow` / `sdwNonDecreasing` / `sdwWellFormed` — the
non-decreasing check reuses the calibrated-clean `cswLe`), the identity/compose/face/degeneracy operations, the
`SimplexWord` word inductive with `sdwEvaluate`, the length-preservation theorem, the simplicial congruence
`SimplexConv` and its soundness `sdwConvSound` (each generating relation discharged by an audited `composeMap_*`
identity), the decision `decideSimplexEq` with both the positive (`decideSimplexEq_ofSimplexConv`) and refutation
(`sdwNotConv_ofDecideFalse`) halves, the capability + wall markers, and the ground fires.

The Eilenberg–Zilber completeness converse is WALLED (`sdwHasEilenbergZilberCompleteness = false`: recovering the
unique surjection-then-injection factorization from an arbitrary table and lifting it to a `SimplexConv` path needs
a `WellFounded.fix` table-complexity recursion, banned here).  The deep ∞-categorical directed univalence /
Segal–Rezk completeness is WALLED (`sdwHasDirectedUnivalence = false`, `sdwHasSegalCompleteness = false`: higher
coherences need `funext` / `Quot.sound`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `funext`,
`WellFounded.fix`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Directed.MonoMap
#assert_no_axioms FX1Poly.Polygraph.Directed.MonoMap.mk
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwLength
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwEntriesBelow
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwNonDecreasing
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwWellFormed
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwSimplexId
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwSimplexCompose
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwFace
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwDegen
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexWord
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexWord.idW
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexWord.faceW
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexWord.degenW
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexWord.compW
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwEvaluate
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwEvaluateTableLength
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexConv
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexConv.refl
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexConv.symm
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexConv.trans
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexConv.congComp
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexConv.assocConv
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexConv.idLeftConv
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexConv.idRightConv
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexConv.faceDegenSame
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexConv.faceDegenSucc
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexConv.faceFace
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexConv.degenDegen
#assert_no_axioms FX1Poly.Polygraph.Directed.SimplexConv.faceDegenLower
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwConvSound
#assert_no_axioms FX1Poly.Polygraph.Directed.decideSimplexEq
#assert_no_axioms FX1Poly.Polygraph.Directed.decideSimplexEq_ofSimplexConv
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwNotConv_ofDecideFalse
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwHasEilenbergZilberCompleteness
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwHasDirectedUnivalence
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwHasSegalCompleteness
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwHasSimplexWordDecision
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwFire_faceFaceDecides
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwFire_faceFaceConvDecides
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwFire_triangleDecides
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwFire_idComposeDecides
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwFire_distinctDecidesFalse
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwFire_faceSkipTable
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwFire_degenRepeatTable
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwFire_wellFormedFace
#assert_no_axioms FX1Poly.Polygraph.Directed.sdwFire_wellFormedComposite

end FX1PolyAudit
