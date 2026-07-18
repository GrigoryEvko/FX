import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingFreeGroup.FreeGroupSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingFreeGroup.FreeGroupSeed — zero-axiom gate (the FULLY DECIDED
walking free NON-abelian group on an ARBITRARY alphabet, decided by free-reduction to reduced words)

Per-declaration zero-axiom gate for the walking free group on `ℕ`: the `Bool`/`Nat` colour-comparison kit
(`natBeqSelfTrue`/`natBeqImpliesEq`/`natBeqSymmEq`, `boolDiffer` and its algebra), the `SignedGen` alphabet and
`isInverseGen`/`flipGen` with their inverse relations, the cons-only reducer (`reduceCons`/`appendReduce`/
`reduceWord`/`snoc`/`invertInto`/`invertWord`, NO `List.append`), the `IsReduced` predicate, the confluence
crux (`reduceConsCancelInverse`, `appendReduceReduceConsSwap`, `appendReduceAssoc`, `appendReduceReduceLeft`),
the `snoc`/`invertWord` algebra, the inverse-cancellation and reversed inverse-homomorphism word lemmas
(`appendReduceInvertLeft`/`Right`, `invertReduceCons`, `invertAppendReduceReversed`), the `FreeGroupTree`
carrier + `wordOf` fold + `wordOfIsReduced`, the twelve-law + congruence + equivalence `FreeGroupTreeConv` (NO
`commSwap`, REVERSED `invHomReversed`), soundness, the `genTree`/`combOfWord` normalization chain, completeness,
the decision biconditional, the total decider + instance, the cancellation / non-commutativity / reversed-inv /
rejection groundings, and the marker.  The whole decision must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`, `Int`, `Nat.sub` — only `Nat.beq` structural facts and cons-only list
algebra. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natBeqSelfTrue
#assert_no_axioms FX1Poly.Polygraph.natBeqImpliesEq
#assert_no_axioms FX1Poly.Polygraph.natBeqSymmEq
#assert_no_axioms FX1Poly.Polygraph.boolNotInvol
#assert_no_axioms FX1Poly.Polygraph.boolNotTrue
#assert_no_axioms FX1Poly.Polygraph.boolNotFalse
#assert_no_axioms FX1Poly.Polygraph.boolNotEqTrueImpliesFalse
#assert_no_axioms FX1Poly.Polygraph.boolNotEqFalseImpliesTrue
#assert_no_axioms FX1Poly.Polygraph.boolAndTrueLeft
#assert_no_axioms FX1Poly.Polygraph.boolAndTrueRight
#assert_no_axioms FX1Poly.Polygraph.boolDiffer
#assert_no_axioms FX1Poly.Polygraph.boolDifferComm
#assert_no_axioms FX1Poly.Polygraph.boolDifferNotBoth
#assert_no_axioms FX1Poly.Polygraph.boolDifferNotSelfLeft
#assert_no_axioms FX1Poly.Polygraph.boolDifferTrueImpliesNot
#assert_no_axioms FX1Poly.Polygraph.SignedGen
#assert_no_axioms FX1Poly.Polygraph.isInverseGen
#assert_no_axioms FX1Poly.Polygraph.flipGen
#assert_no_axioms FX1Poly.Polygraph.flipGenInvol
#assert_no_axioms FX1Poly.Polygraph.isInverseGenComm
#assert_no_axioms FX1Poly.Polygraph.isInverseGenToFlip
#assert_no_axioms FX1Poly.Polygraph.isInverseGenFlipBoth
#assert_no_axioms FX1Poly.Polygraph.isInverseGenFlipLeftTrue
#assert_no_axioms FX1Poly.Polygraph.reduceCons
#assert_no_axioms FX1Poly.Polygraph.reduceConsConsTrue
#assert_no_axioms FX1Poly.Polygraph.reduceConsConsFalse
#assert_no_axioms FX1Poly.Polygraph.appendReduce
#assert_no_axioms FX1Poly.Polygraph.reduceWord
#assert_no_axioms FX1Poly.Polygraph.snoc
#assert_no_axioms FX1Poly.Polygraph.invertInto
#assert_no_axioms FX1Poly.Polygraph.invertWord
#assert_no_axioms FX1Poly.Polygraph.reduceWordCancelsInversePair
#assert_no_axioms FX1Poly.Polygraph.reduceWordKeepsDistinct
#assert_no_axioms FX1Poly.Polygraph.invertWordReversesFlips
#assert_no_axioms FX1Poly.Polygraph.IsReduced
#assert_no_axioms FX1Poly.Polygraph.isReducedTail
#assert_no_axioms FX1Poly.Polygraph.reduceConsPreservesReduced
#assert_no_axioms FX1Poly.Polygraph.appendReducePreservesReduced
#assert_no_axioms FX1Poly.Polygraph.reduceConsCancelInverse
#assert_no_axioms FX1Poly.Polygraph.appendReduceReduceConsSwap
#assert_no_axioms FX1Poly.Polygraph.appendReduceAssoc
#assert_no_axioms FX1Poly.Polygraph.reduceWordReducedFixed
#assert_no_axioms FX1Poly.Polygraph.appendReduceReduceLeft
#assert_no_axioms FX1Poly.Polygraph.appendReduceSnoc
#assert_no_axioms FX1Poly.Polygraph.isLastNotInverse
#assert_no_axioms FX1Poly.Polygraph.isLastNotInverseOfSnoc
#assert_no_axioms FX1Poly.Polygraph.appendReduceSingletonSnoc
#assert_no_axioms FX1Poly.Polygraph.invertIntoSnocComm
#assert_no_axioms FX1Poly.Polygraph.invertWordCons
#assert_no_axioms FX1Poly.Polygraph.invertWordSnoc
#assert_no_axioms FX1Poly.Polygraph.invertWordInvolution
#assert_no_axioms FX1Poly.Polygraph.snocPreservesReduced
#assert_no_axioms FX1Poly.Polygraph.invertPreservesReduced
#assert_no_axioms FX1Poly.Polygraph.appendReduceInvertLeft
#assert_no_axioms FX1Poly.Polygraph.appendReduceInvertRight
#assert_no_axioms FX1Poly.Polygraph.invertReduceCons
#assert_no_axioms FX1Poly.Polygraph.invertAppendReduceReversed
#assert_no_axioms FX1Poly.Polygraph.FreeGroupTree
#assert_no_axioms FX1Poly.Polygraph.wordOf
#assert_no_axioms FX1Poly.Polygraph.wordOfIsReduced
#assert_no_axioms FX1Poly.Polygraph.FreeGroupTreeConv
#assert_no_axioms FX1Poly.Polygraph.freeGroupTreeConv_sound
#assert_no_axioms FX1Poly.Polygraph.genTree
#assert_no_axioms FX1Poly.Polygraph.genTreePositive
#assert_no_axioms FX1Poly.Polygraph.genTreeNegative
#assert_no_axioms FX1Poly.Polygraph.combOfWord
#assert_no_axioms FX1Poly.Polygraph.genTreeInverseCancels
#assert_no_axioms FX1Poly.Polygraph.invGenTree
#assert_no_axioms FX1Poly.Polygraph.combReduceCons
#assert_no_axioms FX1Poly.Polygraph.combOfWordAppendReduce
#assert_no_axioms FX1Poly.Polygraph.combOfWordSnoc
#assert_no_axioms FX1Poly.Polygraph.combOfWordInvert
#assert_no_axioms FX1Poly.Polygraph.freeGroupTreeReducesToComb
#assert_no_axioms FX1Poly.Polygraph.freeGroupTreeConv_complete
#assert_no_axioms FX1Poly.Polygraph.freeGroupTreeConv_iff_reducedWord
#assert_no_axioms FX1Poly.Polygraph.decideFreeGroupTreeConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableFreeGroupTreeConv
#assert_no_axioms FX1Poly.Polygraph.freeGroupCancellationHolds
#assert_no_axioms FX1Poly.Polygraph.freeGroupNonCommutative
#assert_no_axioms FX1Poly.Polygraph.freeGroupInverseHomReversedHolds
#assert_no_axioms FX1Poly.Polygraph.freeGroupRejectsUnit
#assert_no_axioms FX1Poly.Polygraph.fxWalkingFreeGroup_hasReducedWordDecision

end FX1PolyAudit
