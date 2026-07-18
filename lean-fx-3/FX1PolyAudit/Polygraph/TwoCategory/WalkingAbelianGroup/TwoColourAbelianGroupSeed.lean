import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAbelianGroup.TwoColourAbelianGroupSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAbelianGroup.TwoColourAbelianGroupSeed — zero-axiom gate (the
FULLY DECIDED walking free abelian group on TWO generators = walking ℤ²)

Per-declaration zero-axiom gate for the walking free abelian group of rank 2: the
`TwoColourAbelianGroupTree` carrier, the two difference-pair winding folds (`windingAOf`/`windingBOf`, ℤ² as a
pair of ℕ²/~ — NO `Int`, NO `Nat.sub`) with their smokes, the 14-constructor `TwoColourAbelianGroupTreeConv`,
the two soundness components, the four comb families / two pair-forms / two-colour `normalFormOf`, the
carrier-specific `twoColourConvOfTreeEq`/`twoColourConvMiddleFour`, the four concat lemmas, the two per-colour
pair-form merges, the four inverse-push lemmas, the two pair-form inverse-swaps, the four-way `normalMerge`,
normalization (`toNormalFormConv`), the two pumps + two iterated pumps, the two per-colour pair-form
equivalences, completeness, the decision biconditional, the total decider + instance, the cancellation /
rejection / inverse-distribution groundings, and the marker.  The whole decision (soundness + normalization +
completeness + decider) must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega` — only the colour-agnostic winding kit reused from the single-generator sibling plus
`Nat.add_comm`/`Nat.add_assoc`/`Nat.add_zero` + structural `Nat.succ.inj` cancellation.  The reused
`AbelianGroupSeed` primitives (`WindingCount`/`windingEquiv`/`windingMul`/`windingInv`/`natZeroAdd`/… and the
`windingEquiv` equivalence + congruence lemmas) are gated in that file's own twin and NOT re-asserted here. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.TwoColourAbelianGroupTree
#assert_no_axioms FX1Poly.Polygraph.windingAOf
#assert_no_axioms FX1Poly.Polygraph.windingBOf
#assert_no_axioms FX1Poly.Polygraph.windingAOf_leafA
#assert_no_axioms FX1Poly.Polygraph.windingBOf_leafA
#assert_no_axioms FX1Poly.Polygraph.windingAOf_invLeafA
#assert_no_axioms FX1Poly.Polygraph.TwoColourAbelianGroupTreeConv
#assert_no_axioms FX1Poly.Polygraph.twoColourAbelianGroupConv_soundA
#assert_no_axioms FX1Poly.Polygraph.twoColourAbelianGroupConv_soundB
#assert_no_axioms FX1Poly.Polygraph.combPosA
#assert_no_axioms FX1Poly.Polygraph.combNegA
#assert_no_axioms FX1Poly.Polygraph.combPosB
#assert_no_axioms FX1Poly.Polygraph.combNegB
#assert_no_axioms FX1Poly.Polygraph.pairFormA
#assert_no_axioms FX1Poly.Polygraph.pairFormB
#assert_no_axioms FX1Poly.Polygraph.normalFormOf
#assert_no_axioms FX1Poly.Polygraph.twoColourConvOfTreeEq
#assert_no_axioms FX1Poly.Polygraph.twoColourConvMiddleFour
#assert_no_axioms FX1Poly.Polygraph.combPosAConcat
#assert_no_axioms FX1Poly.Polygraph.combNegAConcat
#assert_no_axioms FX1Poly.Polygraph.combPosBConcat
#assert_no_axioms FX1Poly.Polygraph.combNegBConcat
#assert_no_axioms FX1Poly.Polygraph.pairFormAMerge
#assert_no_axioms FX1Poly.Polygraph.pairFormBMerge
#assert_no_axioms FX1Poly.Polygraph.invCombPosA
#assert_no_axioms FX1Poly.Polygraph.invCombNegA
#assert_no_axioms FX1Poly.Polygraph.invCombPosB
#assert_no_axioms FX1Poly.Polygraph.invCombNegB
#assert_no_axioms FX1Poly.Polygraph.invPairFormASwap
#assert_no_axioms FX1Poly.Polygraph.invPairFormBSwap
#assert_no_axioms FX1Poly.Polygraph.normalMerge
#assert_no_axioms FX1Poly.Polygraph.toNormalFormConv
#assert_no_axioms FX1Poly.Polygraph.pairFormAPump
#assert_no_axioms FX1Poly.Polygraph.pairFormBPump
#assert_no_axioms FX1Poly.Polygraph.pairFormAPumpN
#assert_no_axioms FX1Poly.Polygraph.pairFormBPumpN
#assert_no_axioms FX1Poly.Polygraph.pairFormAEquivConv
#assert_no_axioms FX1Poly.Polygraph.pairFormBEquivConv
#assert_no_axioms FX1Poly.Polygraph.twoColourAbelianGroupConv_complete
#assert_no_axioms FX1Poly.Polygraph.twoColourAbelianGroupConv_iff_windingEquiv
#assert_no_axioms FX1Poly.Polygraph.decideTwoColourAbelianGroupTreeConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableTwoColourAbelianGroupTreeConv
#assert_no_axioms FX1Poly.Polygraph.twoColourAbelianGroupCancellationHolds
#assert_no_axioms FX1Poly.Polygraph.twoColourAbelianGroupRejectsLeafAB
#assert_no_axioms FX1Poly.Polygraph.twoColourAbelianGroupInverseDistributes
#assert_no_axioms FX1Poly.Polygraph.fxWalkingAbelianGroup_hasTwoColourDecision

end FX1PolyAudit
