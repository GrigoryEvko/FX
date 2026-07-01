import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionSaturatedNormalization

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionSaturatedNormalization — zero-axiom gate (fib-3 dim-2 relative SN)

Per-declaration zero-axiom gate for the KB-completed walking-adjunction rewrite's strong normalization RELATIVE
TO the structural floor: the two count-preserving-implies-structural embeddings (the KB completion adds only
generator-count-strictly-decreasing rules), and the two relative-SN theorems (saturated rewrite is SN given the
structural `TwoCellStep` floor, via fuel-bounded lexicographic `Acc` descent).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- ★ The KB completion adds only count-decreasing rules: count-preserving saturated ⟹ structural
#assert_no_axioms FX1Poly.Tier0.AdjunctionLeftSaturatedStep.generatorCountPreserving_isStructural
#assert_no_axioms FX1Poly.Tier0.AdjunctionRightSaturatedStep.generatorCountPreserving_isStructural

-- ★ The saturated rewrite is strongly normalizing RELATIVE TO the structural floor
#assert_no_axioms FX1Poly.Tier0.adjunctionLeftSaturated_isStronglyNormalizing
#assert_no_axioms FX1Poly.Tier0.adjunctionRightSaturated_isStronglyNormalizing

end FX1PolyAudit
