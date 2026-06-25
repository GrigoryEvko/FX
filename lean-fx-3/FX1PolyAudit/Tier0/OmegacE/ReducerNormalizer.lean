import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.OmegacE.ReducerNormalizer

/-! # FX1PolyAudit.Tier0.OmegacE.ReducerNormalizer

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.OmegacE.ReducerNormalizer`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- NORMALIZER FROM TERMINATION + REDUCER (ReducerNormalizer.lean): the word analog of RawTerm.normalize.
-- WordReducer (sound+complete reduceOnce) + IsTerminating ⟹ a WordNormalizer (toNormalizer), via Acc.rec
-- driving reduceOnce along the termination accessibility (normalize_reaches/normalize_blocksStep correctness;
-- Acc.rec axiom-free). CAPSTONE decidableConvertibleModulo_ofConvergent: local confluence + termination +
-- reducer ⟹ decidable word problem (newman → toNormalizer → decidableOfNormalizer) — the full convergent-
-- presentation decidability, every hypothesis checkable for a concrete system.
#assert_no_axioms FX1Poly.OmegacE.WordReducer

#assert_no_axioms FX1Poly.OmegacE.WordReducer.normalize

#assert_no_axioms FX1Poly.OmegacE.WordReducer.normalize_unfold

#assert_no_axioms FX1Poly.OmegacE.WordReducer.normalize_reaches

#assert_no_axioms FX1Poly.OmegacE.WordReducer.normalize_blocksStep

#assert_no_axioms FX1Poly.OmegacE.WordReducer.toNormalizer

#assert_no_axioms FX1Poly.OmegacE.decidableConvertibleModulo_ofConvergent

end FX1PolyAudit
