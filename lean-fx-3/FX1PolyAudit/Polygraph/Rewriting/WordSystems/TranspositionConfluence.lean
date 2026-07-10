import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.OmegacE.TranspositionConfluence

/-! # FX1PolyAudit.Polygraph.OmegacE.TranspositionConfluence

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.OmegacE.TranspositionConfluence`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- TRANSPOSITION CONFLUENCE (TranspositionConfluence.lean): the convergence proof. The single rule
-- [a,b]→[b,a] has NO self-overlap (overlap would force a=b), so it is ORTHOGONAL — the prefix-trichotomy's
-- one-cell-overlap case is VACUOUS (absurd … distinct), unlike idempotent's real [c,c,c] critical pair.
-- transpositionRewriteOneStep_decomposition/ofDecomposition (structural inversion) → transpositionJoinableWhenLeftShorter
-- (disjoint redexes commute) → transpositionHasLocalConfluence → transpositionHasConfluence (newman + the
-- termination). Generic word-list helpers reused from IdempotentConfluence; disjoint-case word equalities via
-- explicit-arg rw chains (simp only pulls propext from its machinery). All zero-axiom. A WordReducer for the
-- decidable word problem is the slice below.
#assert_no_axioms FX1Poly.OmegacE.transpositionRewriteOneStep_decomposition

#assert_no_axioms FX1Poly.OmegacE.transpositionRewriteOneStep_ofDecomposition

#assert_no_axioms FX1Poly.OmegacE.transpositionJoinableWhenLeftShorter

#assert_no_axioms FX1Poly.OmegacE.transpositionHasLocalConfluence

#assert_no_axioms FX1Poly.OmegacE.transpositionHasConfluence

end FX1PolyAudit
