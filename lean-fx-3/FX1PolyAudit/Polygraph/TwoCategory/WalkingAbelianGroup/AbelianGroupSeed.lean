import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAbelianGroup.AbelianGroupSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAbelianGroup.AbelianGroupSeed — zero-axiom gate (the FULLY
DECIDED walking free abelian group on one generator = walking ℤ, single generator)

Per-declaration zero-axiom gate for the walking free abelian group of rank 1: the `AbelianGroupTree`
carrier, the difference-pair `WindingCount` soundness invariant (ℤ as ℕ²/~, additive only — NO `Int`, NO
`Nat.sub`), `windingOf`/`windingEquiv`, the nine-law + congruence + equivalence `AbelianGroupTreeConv`,
the pure-Nat arithmetic helpers (`natZeroAdd`/`addMiddleFour`/`addExchange`/`natAddRightCancel`), the
`windingEquiv` equivalence + congruences, soundness, the `combPos`/`combNeg`/`pairForm` normalization chain
+ the pump lemmas, completeness, the decision biconditional, the total decider, the cancellation / rejection
/ inverse-distribution groundings, and the marker.  The whole decision (soundness + normalization +
completeness + decider) must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega` — only `Nat.add_comm`/`Nat.add_assoc`/`Nat.add_zero` + structural `Nat.succ.inj` cancellation. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.AbelianGroupTree
#assert_no_axioms FX1Poly.Polygraph.WindingCount
#assert_no_axioms FX1Poly.Polygraph.windingOf
#assert_no_axioms FX1Poly.Polygraph.windingEquiv
#assert_no_axioms FX1Poly.Polygraph.windingMul
#assert_no_axioms FX1Poly.Polygraph.windingInv
#assert_no_axioms FX1Poly.Polygraph.AbelianGroupTreeConv
#assert_no_axioms FX1Poly.Polygraph.windingOf_leaf
#assert_no_axioms FX1Poly.Polygraph.windingOf_unit
#assert_no_axioms FX1Poly.Polygraph.windingOf_invLeaf
#assert_no_axioms FX1Poly.Polygraph.natZeroAdd
#assert_no_axioms FX1Poly.Polygraph.addMiddleFour
#assert_no_axioms FX1Poly.Polygraph.addExchange
#assert_no_axioms FX1Poly.Polygraph.abelianGroupNatAddRightCancel
#assert_no_axioms FX1Poly.Polygraph.windingEquivRefl
#assert_no_axioms FX1Poly.Polygraph.windingEquivSymm
#assert_no_axioms FX1Poly.Polygraph.windingEquivTrans
#assert_no_axioms FX1Poly.Polygraph.windingEquivMulCongr
#assert_no_axioms FX1Poly.Polygraph.windingEquivInvCongr
#assert_no_axioms FX1Poly.Polygraph.abelianGroupTreeConv_sound
#assert_no_axioms FX1Poly.Polygraph.convOfTreeEq
#assert_no_axioms FX1Poly.Polygraph.convMiddleFour
#assert_no_axioms FX1Poly.Polygraph.combPos
#assert_no_axioms FX1Poly.Polygraph.combNeg
#assert_no_axioms FX1Poly.Polygraph.combPosConcat
#assert_no_axioms FX1Poly.Polygraph.combNegConcat
#assert_no_axioms FX1Poly.Polygraph.pairForm
#assert_no_axioms FX1Poly.Polygraph.pairFormMerge
#assert_no_axioms FX1Poly.Polygraph.invCombPos
#assert_no_axioms FX1Poly.Polygraph.invCombNeg
#assert_no_axioms FX1Poly.Polygraph.invPairFormSwap
#assert_no_axioms FX1Poly.Polygraph.toPairFormConv
#assert_no_axioms FX1Poly.Polygraph.pairFormPump
#assert_no_axioms FX1Poly.Polygraph.pairFormPumpN
#assert_no_axioms FX1Poly.Polygraph.pairFormEquivConv
#assert_no_axioms FX1Poly.Polygraph.abelianGroupTreeConv_complete
#assert_no_axioms FX1Poly.Polygraph.abelianGroupTreeConv_iff_windingEquiv
#assert_no_axioms FX1Poly.Polygraph.decideAbelianGroupTreeConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableAbelianGroupTreeConv
#assert_no_axioms FX1Poly.Polygraph.abelianGroupCancellationHolds
#assert_no_axioms FX1Poly.Polygraph.abelianGroupRejectsLeafUnit
#assert_no_axioms FX1Poly.Polygraph.abelianGroupInverseDistributes
#assert_no_axioms FX1Poly.Polygraph.fxWalkingAbelianGroup_hasSingleGeneratorDecision

end FX1PolyAudit
