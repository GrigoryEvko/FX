import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Decision.ReducedOrderedDecisionTree

/-! # FX1PolyAudit/ComputerAlgebra/Decision/ReducedOrderedDecisionTree — zero-axiom gate
    (the ROBDD half of canonical Boolean-equivalence decision)

Per-declaration zero-axiom gate for the reduced-ordered-binary-decision-TREE engine: the
hand-rolled Bool/Nat kits (conjunction/disjunction intro-elim, `robddBoolBeq`,
`robddBoolXor`, `Nat.beq` reflexivity/soundness, the strict comparison `robddNatLess` with
beq-separation, transitivity and trichotomy), single-point environment updates with their
two read lemmas, the `RobddTree` carrier with structural beq (reflexivity + soundness) and
evaluation, the Boolean invariants (`robddAllVarsAbove` with weakening, `robddIsOrdered`,
`robddIsReduced`, `robddIsCanonical`), the independence lemma
(`robddEvalUpdateIndependent`) and the two cofactor readers, ★ CANONICITY
(`robddCanonicalUnique` — canonical trees computing the same function pointwise are
structurally equal, by nested structural induction, no fuel), the `RobddFormula` carrier
with evaluation, restriction (eval-compatible, coverage-preserving), pointwise evaluation
congruence and Shannon expansion, the sorted-dedup support machinery (insertion preserves
order/membership/bounds, accumulation covers and sorts), the Shannon builder
`robddBuildOver` through the collapsing constructor `robddMkBranch` (canonical by
construction, evaluation-correct over covering lists), the merged-support decision
procedure `robddDecideEquiv`, the biconditional `robddEquivIffDecide`, the `Decidable`
instance `robddFormulaEquivDecidable`, and the DECIDED marker
`fxDissatBool_hasRobddDecision = true`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.robddBoolAndElim
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBoolAndIntro
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBoolOrElim
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBoolOrIntroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBoolOrIntroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBoolNotElim
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBoolCondSame
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBoolBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBoolBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBoolBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBoolXor
#assert_no_axioms FX1Poly.ComputerAlgebra.robddNatBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.robddNatBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.robddNatLess
#assert_no_axioms FX1Poly.ComputerAlgebra.robddNatLessImpliesBeqFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.robddNatLessTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.robddNatTrichotomy
#assert_no_axioms FX1Poly.ComputerAlgebra.robddEnvUpdate
#assert_no_axioms FX1Poly.ComputerAlgebra.robddEnvUpdateAtTarget
#assert_no_axioms FX1Poly.ComputerAlgebra.robddEnvUpdateAway
#assert_no_axioms FX1Poly.ComputerAlgebra.RobddTree
#assert_no_axioms FX1Poly.ComputerAlgebra.robddTreeBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.robddTreeBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.robddTreeBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.robddEval
#assert_no_axioms FX1Poly.ComputerAlgebra.robddAllVarsAbove
#assert_no_axioms FX1Poly.ComputerAlgebra.robddIsOrdered
#assert_no_axioms FX1Poly.ComputerAlgebra.robddIsReduced
#assert_no_axioms FX1Poly.ComputerAlgebra.robddIsCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.robddAllVarsAboveWeaken
#assert_no_axioms FX1Poly.ComputerAlgebra.robddEvalUpdateIndependent
#assert_no_axioms FX1Poly.ComputerAlgebra.robddCofactorLow
#assert_no_axioms FX1Poly.ComputerAlgebra.robddCofactorHigh
#assert_no_axioms FX1Poly.ComputerAlgebra.robddCanonicalBranchParts
#assert_no_axioms FX1Poly.ComputerAlgebra.robddReducednessAbsurd
#assert_no_axioms FX1Poly.ComputerAlgebra.robddCanonicalUnique
#assert_no_axioms FX1Poly.ComputerAlgebra.RobddFormula
#assert_no_axioms FX1Poly.ComputerAlgebra.robddFormulaEval
#assert_no_axioms FX1Poly.ComputerAlgebra.robddRestrict
#assert_no_axioms FX1Poly.ComputerAlgebra.robddRestrictEval
#assert_no_axioms FX1Poly.ComputerAlgebra.robddFormulaEvalCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.robddShannonExpansion
#assert_no_axioms FX1Poly.ComputerAlgebra.robddListContains
#assert_no_axioms FX1Poly.ComputerAlgebra.robddListAllAbove
#assert_no_axioms FX1Poly.ComputerAlgebra.robddListSortedStrict
#assert_no_axioms FX1Poly.ComputerAlgebra.robddSortedInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.robddListAllAboveWeaken
#assert_no_axioms FX1Poly.ComputerAlgebra.robddListAllAboveInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.robddSortedInsertPreserves
#assert_no_axioms FX1Poly.ComputerAlgebra.robddContainsInsertSelf
#assert_no_axioms FX1Poly.ComputerAlgebra.robddContainsInsertMono
#assert_no_axioms FX1Poly.ComputerAlgebra.robddSupportInto
#assert_no_axioms FX1Poly.ComputerAlgebra.robddContainsSupportMono
#assert_no_axioms FX1Poly.ComputerAlgebra.robddSupportIntoSorted
#assert_no_axioms FX1Poly.ComputerAlgebra.robddFormulaVarsCovered
#assert_no_axioms FX1Poly.ComputerAlgebra.robddCoveredMono
#assert_no_axioms FX1Poly.ComputerAlgebra.robddSupportIntoCovers
#assert_no_axioms FX1Poly.ComputerAlgebra.robddRestrictCovered
#assert_no_axioms FX1Poly.ComputerAlgebra.robddCoveredNilConst
#assert_no_axioms FX1Poly.ComputerAlgebra.robddMkBranch
#assert_no_axioms FX1Poly.ComputerAlgebra.robddMkBranchEval
#assert_no_axioms FX1Poly.ComputerAlgebra.robddMkBranchAllVarsAbove
#assert_no_axioms FX1Poly.ComputerAlgebra.robddMkBranchOrdered
#assert_no_axioms FX1Poly.ComputerAlgebra.robddMkBranchReduced
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBuildOver
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBuildOverAllVarsAbove
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBuildOverOrdered
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBuildOverReduced
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBuildOverCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.robddBuildOverEval
#assert_no_axioms FX1Poly.ComputerAlgebra.robddMergedSupport
#assert_no_axioms FX1Poly.ComputerAlgebra.robddMergedSupportSorted
#assert_no_axioms FX1Poly.ComputerAlgebra.robddMergedSupportCoversLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.robddMergedSupportCoversRight
#assert_no_axioms FX1Poly.ComputerAlgebra.robddDecideEquiv
#assert_no_axioms FX1Poly.ComputerAlgebra.robddEquivIffDecide
#assert_no_axioms FX1Poly.ComputerAlgebra.robddFormulaEquivDecidable
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatBool_hasRobddDecision
#assert_no_axioms FX1Poly.ComputerAlgebra.RobddTree.leaf
#assert_no_axioms FX1Poly.ComputerAlgebra.RobddTree.branch
#assert_no_axioms FX1Poly.ComputerAlgebra.RobddFormula.falseConst
#assert_no_axioms FX1Poly.ComputerAlgebra.RobddFormula.trueConst
#assert_no_axioms FX1Poly.ComputerAlgebra.RobddFormula.variableRef
#assert_no_axioms FX1Poly.ComputerAlgebra.RobddFormula.negation
#assert_no_axioms FX1Poly.ComputerAlgebra.RobddFormula.conjunction
#assert_no_axioms FX1Poly.ComputerAlgebra.RobddFormula.disjunction
#assert_no_axioms FX1Poly.ComputerAlgebra.RobddFormula.exclusiveOr

end FX1PolyAudit
