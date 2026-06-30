import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.OmegacE.TranspositionReducer

/-! # FX1PolyAudit.Polygraph.OmegacE.TranspositionReducer

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.OmegacE.TranspositionReducer`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- TRANSPOSITION REDUCER + DECIDABLE WORD PROBLEM (TranspositionReducer.lean): bounded-search decidability for
-- the length-PRESERVING swap system, mirroring the idempotent reducer with a length-preserving rule.
-- transpositionReduceCells (leftmost-[a,b] scan, splice to [b,a]) with soundness (a splice IS a RewritesOneStep
-- via transpositionRule_fires under context) and completeness (transpositionRewrite_implies_reduceCells_isSome:
-- every step means the scan finds a redex, via the two append-monotonicity lemmas). transpositionWordReducer
-- bundles them (NO distinctness needed — sound/complete hold even at a=b); then
-- decidableConvertibleModulo_transpositionSystem = decidableConvertibleModulo_ofConvergent fed the orthogonal
-- local confluence + the inversion-measure termination (needs a≠b) + this reducer = the FIRST fully-decided
-- length-PRESERVING ωcE system (genuine Newman, length is no measure). The generic option_isSome_map is reused
-- from IdempotentReducer. propext-clean: nomatch/Bool.noConfusion (not simp-to-True), dsimp+if_pos⟨rfl,rfl⟩,
-- and simp only unfolds ONLY the scanner's own equations (never list-append lemmas, whose simp machinery leaks propext).
#assert_no_axioms FX1Poly.OmegacE.transpositionReduceCells

#assert_no_axioms FX1Poly.OmegacE.transpositionReduceCells_fires

#assert_no_axioms FX1Poly.OmegacE.transpositionReduceCells_isSome_append_right

#assert_no_axioms FX1Poly.OmegacE.transpositionReduceCells_isSome_append_left

#assert_no_axioms FX1Poly.OmegacE.transpositionReduceCells_sound

#assert_no_axioms FX1Poly.OmegacE.transpositionRewrite_implies_reduceCells_isSome

#assert_no_axioms FX1Poly.OmegacE.transpositionReduceOnce

#assert_no_axioms FX1Poly.OmegacE.transpositionWordReducer

#assert_no_axioms FX1Poly.OmegacE.decidableConvertibleModulo_transpositionSystem

end FX1PolyAudit
