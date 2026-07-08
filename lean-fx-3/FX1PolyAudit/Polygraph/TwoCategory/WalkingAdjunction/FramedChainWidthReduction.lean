import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.FramedChainWidthReduction

/-! # FX1PolyAudit/…/FramedChainWidthReduction — zero-axiom gate

Per-declaration zero-axiom gate for the Riehl–Verity Prop 3.3.4 middle-four WIDTH-REDUCTION shipped as a
`SaturatedTwoCellConv`-valued STRUCTURAL recursion on the matched-pair width: the per-atom readback frame
(`spineAtomFrame`), the readback-`cons` bridge (`framedChainConsReadback`, `rfl`), the middle-four STEP
(`matchedSnakeTowerLayerStraightens` = the shipped `snakePrefixStraightens`), the WIDTH INDUCTION to the identity
base (`matchedSnakeTowerCell_collapses`, structural on the `MatchedSnakeTowerCell` — its recursor is exercised
here, so an axiom in the inductive would surface), and the readback-carrier assembly
(`framedChainMatchedTowerCollapses`).  Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`, `WellFounded.fix`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineAtomFrame
#assert_no_axioms FX1Poly.Polygraph.framedChainConsReadback
#assert_no_axioms FX1Poly.Polygraph.matchedSnakeTowerLayerStraightens
#assert_no_axioms FX1Poly.Polygraph.matchedSnakeTowerCell_collapses
#assert_no_axioms FX1Poly.Polygraph.framedChainMatchedTowerCollapses
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasFramedChainWidthReduction

end FX1PolyAudit
