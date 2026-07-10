import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.FreeGroupReducedWord

/-! # FX1PolyAudit/Polygraph/Homology/FreeGroupReducedWord — zero-axiom gate (the free-group
    reduced-word normal form: signed alphabet, right-fold free cancellation, structural reducedness,
    the three normal-form theorems, the group operations, and the concrete cancellation probes)

Per-declaration zero-axiom gate for the WP-2GROUP r1 footing (#2199): the signed alphabet and letter
inverse, `areInverse`, the guarded `consReduced` and the right-fold `reduceWord`, the reducedness
predicate `isReducedWord` and its plumbing, ★ `reduceWordProducesReduced` / `reduceWordFixesReduced` /
`reduceWordIsIdempotent`, the group operations `mulWord` / `invWord` / `oneWord`, `Bool` word equality,
and the concrete evaluation probes.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.inverseLetter
#assert_no_axioms FX1Poly.Polygraph.Homology.areInverse
#assert_no_axioms FX1Poly.Polygraph.Homology.consReducedGuarded
#assert_no_axioms FX1Poly.Polygraph.Homology.consReduced
#assert_no_axioms FX1Poly.Polygraph.Homology.reduceWord
#assert_no_axioms FX1Poly.Polygraph.Homology.consReducedCancel
#assert_no_axioms FX1Poly.Polygraph.Homology.consReducedExtend
#assert_no_axioms FX1Poly.Polygraph.Homology.isReducedStep
#assert_no_axioms FX1Poly.Polygraph.Homology.isReducedFrom
#assert_no_axioms FX1Poly.Polygraph.Homology.isReducedWord
#assert_no_axioms FX1Poly.Polygraph.Homology.isReducedStepImpliesTail
#assert_no_axioms FX1Poly.Polygraph.Homology.isReducedStepImpliesFirstFalse
#assert_no_axioms FX1Poly.Polygraph.Homology.isReducedWordTail
#assert_no_axioms FX1Poly.Polygraph.Homology.isReducedWordHeadNotCancel
#assert_no_axioms FX1Poly.Polygraph.Homology.isReducedWordExtendFront
#assert_no_axioms FX1Poly.Polygraph.Homology.isReducedConsReduced
#assert_no_axioms FX1Poly.Polygraph.Homology.reduceWordProducesReduced
#assert_no_axioms FX1Poly.Polygraph.Homology.reduceWordFixesReduced
#assert_no_axioms FX1Poly.Polygraph.Homology.reduceWordIsIdempotent
#assert_no_axioms FX1Poly.Polygraph.Homology.oneWord
#assert_no_axioms FX1Poly.Polygraph.Homology.mulWord
#assert_no_axioms FX1Poly.Polygraph.Homology.invWord
#assert_no_axioms FX1Poly.Polygraph.Homology.signedLetterBeq
#assert_no_axioms FX1Poly.Polygraph.Homology.wordBeq
#assert_no_axioms FX1Poly.Polygraph.Homology.reduceWordEmptyIsEmpty
#assert_no_axioms FX1Poly.Polygraph.Homology.reduceWordCancelsAdjacentInverse
#assert_no_axioms FX1Poly.Polygraph.Homology.reduceWordCancelsInverseTriple
#assert_no_axioms FX1Poly.Polygraph.Homology.reduceWordCancelsNested
#assert_no_axioms FX1Poly.Polygraph.Homology.mulWordCancelsInverse
#assert_no_axioms FX1Poly.Polygraph.Homology.invWordReversesAndFlips
#assert_no_axioms FX1Poly.Polygraph.Homology.wordBeqReflexiveOnLiteral
#assert_no_axioms FX1Poly.Polygraph.Homology.wordBeqRejectsSignFlip
#assert_no_axioms FX1Poly.Polygraph.Homology.freeGroupReducedWordKitIsComplete

end FX1PolyAudit
