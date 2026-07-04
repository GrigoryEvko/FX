import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedInterchangeFreeStep

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/SaturatedInterchangeFreeStep — zero-axiom gate

Per-declaration zero-axiom gate for the NF-bearing saturated fragment: the relation, its
embedding into the combined rewrite, the inherited strong normalization, the conversion
soundness, and the fragment marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SaturatedStepInterchangeFree
#assert_no_axioms FX1Poly.Polygraph.SaturatedStepInterchangeFree.toSaturatedTwoCellStep
#assert_no_axioms FX1Poly.Polygraph.saturatedStepInterchangeFree_isStronglyNormalizing
#assert_no_axioms FX1Poly.Polygraph.SaturatedStepInterchangeFree.toSaturatedConv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSaturatedInterchangeFreeFragment

end FX1PolyAudit
