import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Invertibility.InvertibilitySet

/-! # FX1PolyAudit/Polygraph/Invertibility/InvertibilitySet — zero-axiom gate

Per-declaration zero-axiom gate for the HL23 Def 4.15 invertibility-set layer: the abstract
`CellStructure`, its `invertibilityWitnessOperator`, the `IsInvertibilitySet` structure with its
`IsPostFixed` bridges, the maximal invertibility set (`eq 𝒟` = coinductive closure), and its membership /
maximality lemmas.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Invertibility.CellStructure
#assert_no_axioms FX1Poly.Polygraph.Invertibility.invertibilityWitnessOperator
#assert_no_axioms FX1Poly.Polygraph.Invertibility.IsInvertibilitySet
#assert_no_axioms FX1Poly.Polygraph.Invertibility.IsInvertibilitySet.isPostFixed
#assert_no_axioms FX1Poly.Polygraph.Invertibility.IsInvertibilitySet.ofPostFixed
#assert_no_axioms FX1Poly.Polygraph.Invertibility.maximalInvertibilitySet
#assert_no_axioms FX1Poly.Polygraph.Invertibility.maximalInvertibilitySet_isInvertibilitySet
#assert_no_axioms FX1Poly.Polygraph.Invertibility.IsInvertibilitySet.subset_maximal
#assert_no_axioms FX1Poly.Polygraph.Invertibility.maximalInvertibilitySet.reverseMember
#assert_no_axioms FX1Poly.Polygraph.Invertibility.maximalInvertibilitySet.unitMember
#assert_no_axioms FX1Poly.Polygraph.Invertibility.maximalInvertibilitySet.counitMember

end FX1PolyAudit
