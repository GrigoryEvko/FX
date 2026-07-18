import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAbelianGroup.ColourAbelianGroupSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAbelianGroup.ColourAbelianGroupSeed — zero-axiom gate (the
FULLY DECIDED walking free abelian group on an ARBITRARY alphabet = ℤᵏ, the free ℤ-module)

Per-declaration zero-axiom gate for the walking free abelian group on `ℕ`: the `ColourAbelianTree` carrier,
the difference-of-two-sorted-multisets winding invariant (`windingColoursOf`/`posColoursOf`/`invColoursOf`,
NO `Int`, NO `Nat.sub`), the multiset cancellation kit (`natBeq` reflexivity/soundness, `deleteFirst`, the
`insertSortedRetract` retract, `insertSortedInjective`, `insertManyLeftCancel`), the `insertMany` block algebra
(`insertManyMiddleFour`/`insertManyPairSortedFixed`/`insertManyBlockComm`/`insertManyExchangeFixed`), the
sorted-fixedness of the winding colour-lists, the `multisetWindingEquiv` equivalence + congruences +
transitivity, the twelve-law + congruence + equivalence `ColourAbelianGroupTreeConv`, soundness, the
`combPosColours`/`combInvColours`/`pairFormColours` normalization chain + the pump lemmas, completeness, the
decision biconditional, the total decider, the cancellation / reorder / inverse-distribution / rejection
groundings, and the marker.  The whole decision must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`, `Nat.sub`, `Int` — only the imported structural `natBle`/`insertSorted`/`insertMany`
algebra plus `natBeq`/`Nat.succ.inj`-style structural facts. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ColourAbelianTree
#assert_no_axioms FX1Poly.Polygraph.windingColoursOf
#assert_no_axioms FX1Poly.Polygraph.posColoursOf
#assert_no_axioms FX1Poly.Polygraph.invColoursOf
#assert_no_axioms FX1Poly.Polygraph.posColoursOf_leaf
#assert_no_axioms FX1Poly.Polygraph.invColoursOf_invLeaf
#assert_no_axioms FX1Poly.Polygraph.posColoursOf_mulSorts
#assert_no_axioms FX1Poly.Polygraph.natBeqRefl
#assert_no_axioms FX1Poly.Polygraph.natBeqSound
#assert_no_axioms FX1Poly.Polygraph.deleteFirst
#assert_no_axioms FX1Poly.Polygraph.deleteFirstConsTrue
#assert_no_axioms FX1Poly.Polygraph.deleteFirstConsFalse
#assert_no_axioms FX1Poly.Polygraph.insertSortedRetract
#assert_no_axioms FX1Poly.Polygraph.insertSortedInjective
#assert_no_axioms FX1Poly.Polygraph.insertManyLeftCancel
#assert_no_axioms FX1Poly.Polygraph.insertManyMiddleFour
#assert_no_axioms FX1Poly.Polygraph.insertManyPairSortedFixed
#assert_no_axioms FX1Poly.Polygraph.insertManyBlockComm
#assert_no_axioms FX1Poly.Polygraph.insertManyExchangeFixed
#assert_no_axioms FX1Poly.Polygraph.windingColoursSortedFixed
#assert_no_axioms FX1Poly.Polygraph.multisetWindingEquiv
#assert_no_axioms FX1Poly.Polygraph.multisetWindingEquivRefl
#assert_no_axioms FX1Poly.Polygraph.multisetWindingEquivSymm
#assert_no_axioms FX1Poly.Polygraph.multisetWindingEquivMulCongr
#assert_no_axioms FX1Poly.Polygraph.multisetWindingEquivInvCongr
#assert_no_axioms FX1Poly.Polygraph.multisetWindingEquivTrans
#assert_no_axioms FX1Poly.Polygraph.ColourAbelianGroupTreeConv
#assert_no_axioms FX1Poly.Polygraph.colourAbelianGroupTreeConv_sound
#assert_no_axioms FX1Poly.Polygraph.combPosColours
#assert_no_axioms FX1Poly.Polygraph.combInvColours
#assert_no_axioms FX1Poly.Polygraph.pairFormColours
#assert_no_axioms FX1Poly.Polygraph.convOfTreeEqColours
#assert_no_axioms FX1Poly.Polygraph.convMiddleFourColours
#assert_no_axioms FX1Poly.Polygraph.combPosInsertSorted
#assert_no_axioms FX1Poly.Polygraph.combInvInsertSorted
#assert_no_axioms FX1Poly.Polygraph.combPosConcatColours
#assert_no_axioms FX1Poly.Polygraph.combInvConcatColours
#assert_no_axioms FX1Poly.Polygraph.pairFormMergeColours
#assert_no_axioms FX1Poly.Polygraph.invCombPosColours
#assert_no_axioms FX1Poly.Polygraph.invCombInvColours
#assert_no_axioms FX1Poly.Polygraph.invPairFormColoursSwap
#assert_no_axioms FX1Poly.Polygraph.toPairFormColoursConv
#assert_no_axioms FX1Poly.Polygraph.pairFormColoursPump
#assert_no_axioms FX1Poly.Polygraph.pairFormColoursPumpMany
#assert_no_axioms FX1Poly.Polygraph.pairFormColoursEquivConv
#assert_no_axioms FX1Poly.Polygraph.colourAbelianGroupTreeConv_complete
#assert_no_axioms FX1Poly.Polygraph.colourAbelianGroupTreeConv_iff_windingEquiv
#assert_no_axioms FX1Poly.Polygraph.decideColourAbelianGroupTreeConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableColourAbelianGroupTreeConv
#assert_no_axioms FX1Poly.Polygraph.colourAbelianGroupCancellationHolds
#assert_no_axioms FX1Poly.Polygraph.colourAbelianGroupReordersColours
#assert_no_axioms FX1Poly.Polygraph.colourAbelianGroupInverseDistributes
#assert_no_axioms FX1Poly.Polygraph.colourAbelianGroupRejectsDistinctColours
#assert_no_axioms FX1Poly.Polygraph.fxWalkingAbelianGroup_hasColourVectorDecision

end FX1PolyAudit
