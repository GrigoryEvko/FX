import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Semigroup.TraceWordProblem

/-! # FX1PolyAudit/ComputerAlgebra/Semigroup/TraceWordProblem — zero-axiom gate
    (NET-2 brick: Mazurkiewicz trace equivalence)

Per-declaration zero-axiom gate for the trace word problem: the Boolean/keep-test
micro-kit, the dependent-pair projection `mztKeepAB` with its append/swap laws, the trace
congruence `MztTraceCongr` with cons-congruence, semantic soundness
(`mztCongrPreservesKeepAB`), the head-bubbling engine `mztBubbleHead` and semantic
completeness `mztProjAgreeComplete` (the Keller / Cartier-Foata theorem), the finite pair
carrier and the Boolean decision `mztDecideTraceEqBool` with its soundness
(`mztDecideSoundOfCongr`), the acceptance-to-projection bridge (`mztDecideToProjAgree`) and
Boolean completeness (`mztDecideCompleteOfDecide`, `mztTraceDecisionCorrect`), the
capability markers, and the ground fires.

The trace word problem is FULLY decided (no wall): the free partially-commutative monoid
word problem needs only structural recursion via the projection criterion — unlike the
finitely-presented commutative case (NET-3 T3), which is walled at Dickson's lemma.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.mztOrTrueRight
#assert_no_axioms FX1Poly.ComputerAlgebra.mztOrAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.mztOrFalseElim
#assert_no_axioms FX1Poly.ComputerAlgebra.mztKeepTestSelfLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.mztKeepTestSelfRight
#assert_no_axioms FX1Poly.ComputerAlgebra.mztKeepAB
#assert_no_axioms FX1Poly.ComputerAlgebra.mztKeepABConsKeep
#assert_no_axioms FX1Poly.ComputerAlgebra.mztKeepABConsDrop
#assert_no_axioms FX1Poly.ComputerAlgebra.mztKeepABAppend
#assert_no_axioms FX1Poly.ComputerAlgebra.MztTraceCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.MztTraceCongr.refl
#assert_no_axioms FX1Poly.ComputerAlgebra.MztTraceCongr.adjacentSwap
#assert_no_axioms FX1Poly.ComputerAlgebra.MztTraceCongr.symm
#assert_no_axioms FX1Poly.ComputerAlgebra.MztTraceCongr.trans
#assert_no_axioms FX1Poly.ComputerAlgebra.mztTraceCongrCons
#assert_no_axioms FX1Poly.ComputerAlgebra.mztKeptPairEq
#assert_no_axioms FX1Poly.ComputerAlgebra.mztKeepABSwapPair
#assert_no_axioms FX1Poly.ComputerAlgebra.mztCongrPreservesKeepAB
#assert_no_axioms FX1Poly.ComputerAlgebra.mztKeepABConsInj
#assert_no_axioms FX1Poly.ComputerAlgebra.mztBubbleHead
#assert_no_axioms FX1Poly.ComputerAlgebra.mztProjAgreeComplete
#assert_no_axioms FX1Poly.ComputerAlgebra.mztMemBool
#assert_no_axioms FX1Poly.ComputerAlgebra.mztMemAppend
#assert_no_axioms FX1Poly.ComputerAlgebra.mztInsertLetter
#assert_no_axioms FX1Poly.ComputerAlgebra.mztDedup
#assert_no_axioms FX1Poly.ComputerAlgebra.mztMemInsertHead
#assert_no_axioms FX1Poly.ComputerAlgebra.mztMemInsertMono
#assert_no_axioms FX1Poly.ComputerAlgebra.mztMemDedup
#assert_no_axioms FX1Poly.ComputerAlgebra.mztPairMemBool
#assert_no_axioms FX1Poly.ComputerAlgebra.mztPairMemAppend
#assert_no_axioms FX1Poly.ComputerAlgebra.mztPairWith
#assert_no_axioms FX1Poly.ComputerAlgebra.mztPairWithMem
#assert_no_axioms FX1Poly.ComputerAlgebra.mztAllPairsFrom
#assert_no_axioms FX1Poly.ComputerAlgebra.mztAllPairsFromMem
#assert_no_axioms FX1Poly.ComputerAlgebra.mztAllPairs
#assert_no_axioms FX1Poly.ComputerAlgebra.mztAllPairsMem
#assert_no_axioms FX1Poly.ComputerAlgebra.mztPairCheckAB
#assert_no_axioms FX1Poly.ComputerAlgebra.mztAllPairsAgree
#assert_no_axioms FX1Poly.ComputerAlgebra.mztDecideTraceEqBool
#assert_no_axioms FX1Poly.ComputerAlgebra.mztAllPairsAgreeOfSemantic
#assert_no_axioms FX1Poly.ComputerAlgebra.mztDecideSoundOfCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.mztAllPairsAgreeExtract
#assert_no_axioms FX1Poly.ComputerAlgebra.mztKeepABReduceFirst
#assert_no_axioms FX1Poly.ComputerAlgebra.mztKeepABReduceSecond
#assert_no_axioms FX1Poly.ComputerAlgebra.mztKeepABEmptyOfAbsent
#assert_no_axioms FX1Poly.ComputerAlgebra.mztDecideToProjAgree
#assert_no_axioms FX1Poly.ComputerAlgebra.mztDecideCompleteOfDecide
#assert_no_axioms FX1Poly.ComputerAlgebra.mztTraceDecisionCorrect
#assert_no_axioms FX1Poly.ComputerAlgebra.mztHasTraceCongruence
#assert_no_axioms FX1Poly.ComputerAlgebra.mztHasProjectionDecision
#assert_no_axioms FX1Poly.ComputerAlgebra.mztHasTraceCompleteness
#assert_no_axioms FX1Poly.ComputerAlgebra.mztFireIndependentSwapTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.mztFireDependentSwapFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.mztFireThreeLetterTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.mztFireControlFalse

end FX1PolyAudit
