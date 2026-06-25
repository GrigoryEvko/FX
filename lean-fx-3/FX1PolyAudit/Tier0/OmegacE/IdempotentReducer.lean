import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.OmegacE.IdempotentReducer

/-! # FX1PolyAudit.Tier0.OmegacE.IdempotentReducer

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.OmegacE.IdempotentReducer`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- IDEMPOTENT REDUCER + TERMINATING NORMALIZER (IdempotentReducer.lean): the searchable engine the idempotent
-- system supplies — idempotentReduceCells (leftmost-redex scan, splice [c,c]→[c]) with soundness (a splice IS
-- a RewritesOneStep via idempotentRule_fires under context) and completeness (idempotentRewrite_implies_
-- reduceCells_isSome: every one-step rewrite means the scan finds a redex, via the append-monotonicity lemmas
-- = the structural inversion of one-step rewriting). idempotentWordReducer bundles them (the first concrete
-- WordReducer that genuinely rewrites — the empty system's is the identity); idempotentWordNormalizer =
-- toNormalizer along the termination = the first terminating normalizer for a non-trivial concrete ωcE
-- system. Scope: decidability also needs HasLocalConfluence (the [c,c,c] critical pair) — the slice below.
-- propext-clean: nomatch/Bool.noConfusion (not simp-to-True), dsimp+if_pos.
#assert_no_axioms FX1Poly.OmegacE.idempotentReduceCells

#assert_no_axioms FX1Poly.OmegacE.idempotentReduceCells_doubled

#assert_no_axioms FX1Poly.OmegacE.option_isSome_map

#assert_no_axioms FX1Poly.OmegacE.idempotentReduceCells_isSome_append_right

#assert_no_axioms FX1Poly.OmegacE.idempotentReduceCells_isSome_append_left

#assert_no_axioms FX1Poly.OmegacE.idempotentReduceCells_sound

#assert_no_axioms FX1Poly.OmegacE.idempotentRewrite_implies_reduceCells_isSome

#assert_no_axioms FX1Poly.OmegacE.idempotentReduceOnce

#assert_no_axioms FX1Poly.OmegacE.idempotentWordReducer

#assert_no_axioms FX1Poly.OmegacE.idempotentWordNormalizer

end FX1PolyAudit
