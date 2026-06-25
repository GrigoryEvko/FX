import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationUnion

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationUnion

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationUnion`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The abstract Geser SN-of-union criterion: reduceLeft SN at a + reduceRight SN everywhere + reduceRight
-- quasi-commutes over reduceLeft implies (reduceLeft union reduceRight) SN at a.  Constructive, Init-only,
-- zero-axiom: nested Acc (outer on reduceLeft-Acc, inner on reduceRight-Acc with the outer IH carried in the
-- motive; quasi-commutation reconstructs the right-descendant's left-predecessors).  The crux for open beta-eta
-- SN, reusable for cubical SN-robustness.
#assert_no_axioms FX1Poly.Core.accDownwardUnionStar

#assert_no_axioms FX1Poly.Core.accUnionInner

#assert_no_axioms FX1Poly.Core.accUnion

end FX1PolyAudit
