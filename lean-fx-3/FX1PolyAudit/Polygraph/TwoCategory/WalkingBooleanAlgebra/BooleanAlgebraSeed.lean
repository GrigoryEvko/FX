import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingBooleanAlgebra.BooleanAlgebraSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingBooleanAlgebra.BooleanAlgebraSeed — zero-axiom gate

Per-declaration zero-axiom gate for the walking bounded Boolean algebra on an arbitrary alphabet: the
`BoolAlgTree` carrier and the `Bool` evaluation `evalBoolAlgTree` with its three smokes, the
`BooleanAlgebraTreeConv` convertibility (bounded-distributive-lattice laws + the two complement laws + the three
congruences), the Boolean-evaluation soundness `booleanAlgebraTreeConv_eval_sound` (a genuine sound separator
deciding non-convertibility), the derived-law witnesses (`booleanAlgebraComplementUnique`,
`booleanAlgebraDoubleComplement`, `booleanAlgebraDeMorganMeet`, `booleanAlgebraDeMorganJoin`), the Shannon
cofactor split `booleanAlgebraCofactorSplit`, the distinct-generator / `⊤ ≠ ⊥` / generator-vs-complement negative
groundings, the complete minterm-DNF scaffolding (`boolAlgGensLength` / `boolAlgMintermOf` / `boolAlgConsAll` /
`boolAlgAllMasks` / `boolAlgMaskEnv` / `boolAlgJoinTrueMinterms` / `boolAlgMintermNF`) with its mask-count / NF
smokes, and the completeness wall marker.  Every landed declaration must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega` — the finite `Bool` case-bashing is structural, the mask
enumeration is cons-only, and no `List.append` (`++`), `Nat.le`/`Nat.ble` lemma, or `Int` is used anywhere. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.BoolAlgTree
#assert_no_axioms FX1Poly.Polygraph.evalBoolAlgTree
#assert_no_axioms FX1Poly.Polygraph.evalBoolAlgTree_gen
#assert_no_axioms FX1Poly.Polygraph.evalBoolAlgTree_meet
#assert_no_axioms FX1Poly.Polygraph.evalBoolAlgTree_compl
#assert_no_axioms FX1Poly.Polygraph.BooleanAlgebraTreeConv
#assert_no_axioms FX1Poly.Polygraph.booleanAlgebraTreeConv_eval_sound
#assert_no_axioms FX1Poly.Polygraph.booleanAlgebraComplementUnique
#assert_no_axioms FX1Poly.Polygraph.booleanAlgebraDoubleComplement
#assert_no_axioms FX1Poly.Polygraph.booleanAlgebraDeMorganMeet
#assert_no_axioms FX1Poly.Polygraph.booleanAlgebraDeMorganJoin
#assert_no_axioms FX1Poly.Polygraph.booleanAlgebraCofactorSplit
#assert_no_axioms FX1Poly.Polygraph.booleanAlgebraSeparatesGenerators
#assert_no_axioms FX1Poly.Polygraph.booleanAlgebraSeparatesTopBot
#assert_no_axioms FX1Poly.Polygraph.booleanAlgebraComplementNontrivial
#assert_no_axioms FX1Poly.Polygraph.boolAlgGensLength
#assert_no_axioms FX1Poly.Polygraph.boolAlgMintermOf
#assert_no_axioms FX1Poly.Polygraph.boolAlgConsAll
#assert_no_axioms FX1Poly.Polygraph.boolAlgAllMasks
#assert_no_axioms FX1Poly.Polygraph.boolAlgMaskEnv
#assert_no_axioms FX1Poly.Polygraph.boolAlgJoinTrueMinterms
#assert_no_axioms FX1Poly.Polygraph.boolAlgMintermNF
#assert_no_axioms FX1Poly.Polygraph.boolAlgAllMasks_zero
#assert_no_axioms FX1Poly.Polygraph.boolAlgAllMasks_one
#assert_no_axioms FX1Poly.Polygraph.boolAlgAllMasks_two
#assert_no_axioms FX1Poly.Polygraph.boolAlgMintermOf_smoke
#assert_no_axioms FX1Poly.Polygraph.boolAlgMintermOf_smokeTwo
#assert_no_axioms FX1Poly.Polygraph.boolAlgMintermNF_smoke
#assert_no_axioms FX1Poly.Polygraph.boolAlgMintermNF_eval_gen
#assert_no_axioms FX1Poly.Polygraph.fxWalkingBooleanAlgebra_completenessWall

end FX1PolyAudit
