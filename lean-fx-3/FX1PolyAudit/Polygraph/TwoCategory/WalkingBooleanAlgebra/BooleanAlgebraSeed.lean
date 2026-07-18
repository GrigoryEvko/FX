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
groundings, the minterm-DNF scaffolding (`boolAlgGensLength` / `boolAlgMintermOf` / `boolAlgConsAll` /
`boolAlgAllMasks` / `boolAlgMaskEnv` / `boolAlgJoinTrueMinterms` / `boolAlgMintermNF`) with its mask-count / NF
smokes, the Conv-level De Morgan laws (`booleanAlgebraDeMorganMeetConv` / `booleanAlgebraDeMorganJoinConv`), the
generator-substitution cofactor operators and the crux paired double inductions (`boolAlgGenRestrictTopPair` /
`boolAlgGenRestrictBotPair`), the full Shannon decomposition (`boolAlgFullShannon`), the recursive Shannon decider
(`boolAlgDecideOnGens`) with both correctness directions, and THE COMPLETE TRUTH-TABLE DECISION
(`decideBooleanAlgebraTreeConv` / `booleanAlgebraTreeConv_iff_truthTable` / the `Decidable` instance
`boolAlgDecidableConv`) plus its decision marker.  Every landed declaration must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the finite `Bool` case-bashing is structural, the
substitution/support machinery recurses structurally, the list plumbing is cons-only, and no `List.append`
(`++`), `Nat.le`/`Nat.ble` lemma, or `Int` is used anywhere. -/

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
#assert_no_axioms FX1Poly.Polygraph.boolAlgComplTop
#assert_no_axioms FX1Poly.Polygraph.boolAlgComplBot
#assert_no_axioms FX1Poly.Polygraph.boolAlgMeetMiddleSwap
#assert_no_axioms FX1Poly.Polygraph.booleanAlgebraDeMorganMeetConv
#assert_no_axioms FX1Poly.Polygraph.booleanAlgebraDeMorganJoinConv
#assert_no_axioms FX1Poly.Polygraph.boolAlgBoolEq
#assert_no_axioms FX1Poly.Polygraph.boolAlgBoolEq_refl
#assert_no_axioms FX1Poly.Polygraph.boolAlgBoolEq_eq
#assert_no_axioms FX1Poly.Polygraph.boolAlgAndTrueLeft
#assert_no_axioms FX1Poly.Polygraph.boolAlgAndTrueRight
#assert_no_axioms FX1Poly.Polygraph.boolAlgNatBeqRefl
#assert_no_axioms FX1Poly.Polygraph.boolAlgNatEqOfBeq
#assert_no_axioms FX1Poly.Polygraph.boolAlgSubstTop
#assert_no_axioms FX1Poly.Polygraph.boolAlgSubstBot
#assert_no_axioms FX1Poly.Polygraph.boolAlgSubstTop_gen_eq
#assert_no_axioms FX1Poly.Polygraph.boolAlgSubstTop_gen_ne
#assert_no_axioms FX1Poly.Polygraph.boolAlgSubstBot_gen_eq
#assert_no_axioms FX1Poly.Polygraph.boolAlgSubstBot_gen_ne
#assert_no_axioms FX1Poly.Polygraph.boolAlgListMem
#assert_no_axioms FX1Poly.Polygraph.boolAlgSupportedBy
#assert_no_axioms FX1Poly.Polygraph.boolAlgSubstTop_supported
#assert_no_axioms FX1Poly.Polygraph.boolAlgSubstBot_supported
#assert_no_axioms FX1Poly.Polygraph.boolAlgFalseEnv
#assert_no_axioms FX1Poly.Polygraph.boolAlgEnvSetTop
#assert_no_axioms FX1Poly.Polygraph.boolAlgEnvSetBot
#assert_no_axioms FX1Poly.Polygraph.boolAlgEval_substTop
#assert_no_axioms FX1Poly.Polygraph.boolAlgEval_substBot
#assert_no_axioms FX1Poly.Polygraph.boolAlgGenRestrictTopPair
#assert_no_axioms FX1Poly.Polygraph.boolAlgGenRestrictBotPair
#assert_no_axioms FX1Poly.Polygraph.boolAlgFullShannon
#assert_no_axioms FX1Poly.Polygraph.boolAlgConstOfBool
#assert_no_axioms FX1Poly.Polygraph.boolAlgMeetConst
#assert_no_axioms FX1Poly.Polygraph.boolAlgJoinConst
#assert_no_axioms FX1Poly.Polygraph.boolAlgComplConst
#assert_no_axioms FX1Poly.Polygraph.boolAlgClosedToConst
#assert_no_axioms FX1Poly.Polygraph.boolAlgCat
#assert_no_axioms FX1Poly.Polygraph.boolAlgListMem_cat
#assert_no_axioms FX1Poly.Polygraph.boolAlgColours
#assert_no_axioms FX1Poly.Polygraph.boolAlgSupported_weaken
#assert_no_axioms FX1Poly.Polygraph.boolAlgSelfSupported
#assert_no_axioms FX1Poly.Polygraph.boolAlgDecideOnGens
#assert_no_axioms FX1Poly.Polygraph.boolAlgDecideOnGens_of_evalAgree
#assert_no_axioms FX1Poly.Polygraph.boolAlgDecideOnGens_toConv
#assert_no_axioms FX1Poly.Polygraph.decideBooleanAlgebraTreeConv
#assert_no_axioms FX1Poly.Polygraph.booleanAlgebraTreeConv_iff_truthTable
#assert_no_axioms FX1Poly.Polygraph.boolAlgDecidableConv
#assert_no_axioms FX1Poly.Polygraph.decideBooleanAlgebraTreeConv_gen_refl
#assert_no_axioms FX1Poly.Polygraph.decideBooleanAlgebraTreeConv_gen_distinct
#assert_no_axioms FX1Poly.Polygraph.decideBooleanAlgebraTreeConv_meetComm_ex
#assert_no_axioms FX1Poly.Polygraph.decideBooleanAlgebraTreeConv_meetCompl_ex
#assert_no_axioms FX1Poly.Polygraph.fxWalkingBooleanAlgebra_hasTruthTableDecision

end FX1PolyAudit
