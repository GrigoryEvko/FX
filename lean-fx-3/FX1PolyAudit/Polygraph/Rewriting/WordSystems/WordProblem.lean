import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.OmegacE.WordProblem

/-! # FX1PolyAudit.Polygraph.OmegacE.WordProblem

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.OmegacE.WordProblem`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- WORD PROBLEM DECIDED (WordProblem.lean): convergent presentation ⟹ decidable convertibility — the Path-B
-- twin of Conv.decidableOfStronglyNormalizing. WordNormalizer (normalize to a reachable normal form) +
-- rigidity (rewritesMany_eq_of_blocksStep) give Joinable = NF-equality, then Church-Rosser gives
-- ConvertibleModulo = NF-equality, hence Decidable (ConvertibleModulo) by decidable_of_iff over the
-- propext-free word DecidableEq. CONDITIONAL on HasConfluence + a WordNormalizer (discharged per concrete
-- system); the convertibility characterization uses Iff.trans, NOT rw [← iff] (which pulls propext).
#assert_no_axioms FX1Poly.OmegacE.WordNormalizer

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.rewritesMany_eq_of_blocksStep

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.Joinable.iff_normalize_eq

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.ConvertibleModulo.iff_normalize_eq

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.ConvertibleModulo.decidableOfNormalizer

end FX1PolyAudit
