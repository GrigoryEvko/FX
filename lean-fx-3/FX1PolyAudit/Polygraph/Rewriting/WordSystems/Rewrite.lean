import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.OmegacE.Rewrite

/-! # FX1PolyAudit.Polygraph.OmegacE.Rewrite

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.OmegacE.Rewrite`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- DIMENSION-2 WORD REWRITING (Rewrite.lean): word equality MODULO a rule system — the structure whose
-- convergence (termination + confluence) is the Makkai word-problem decision. One-step rewriting fires a
-- rule inside any context (congruence by construction); many-step is its reflexive-transitive closure.
-- First invariant: length is preserved under a length-preserving system (one-step + many-step). Plus the
-- algebraic package: many-step is reflexive/transitive + a two-sided append-congruence (monoid-compatible
-- preorder). Scope: the rewriting SUBSTRATE; confluence and decidability are separate slices below.
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.RewritesOneStep

#assert_no_axioms FX1Poly.OmegacE.IsLengthPreservingSystem

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.RewritesOneStep.length_preserved

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.RewritesMany

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.RewritesMany.single

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.RewritesMany.trans

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.RewritesMany.length_preserved

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.RewritesMany.underLeftContext

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.RewritesMany.underRightContext

-- CONVERTIBILITY MODULO A SYSTEM (Rewrite.lean): the reflexive-symmetric-transitive closure of rewriting =
-- equality in the PRESENTED monoid (what the Makkai word problem decides). ConvertibleModulo is an
-- equivalence (so the quotient is well-defined) and a two-sided append-congruence (so the quotient is a
-- monoid); RewritesMany embeds into it (ofRewritesMany). Length is a convertibility invariant under a
-- length-preserving system — the SEPARATING invariant (different lengths ⟹ not convertible).
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.ConvertibleModulo

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.ConvertibleModulo.ofRewritesMany

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.ConvertibleModulo.equivalence

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.ConvertibleModulo.underLeftContext

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.ConvertibleModulo.underRightContext

#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.ConvertibleModulo.length_preserved

end FX1PolyAudit
