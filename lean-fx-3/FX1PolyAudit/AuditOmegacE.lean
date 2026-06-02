import FX1PolyAudit.DependencyAudit
import FX1Poly.OmegacE.WordFreeMonoid
import FX1Poly.OmegacE.WordFreeMonoidUniversal
import FX1Poly.OmegacE.Rewrite

/-! # FX1PolyAudit/AuditOmegacE — zero-axiom gates for the ωcE / Makkai word-problem leg

Per-declaration `#assert_no_axioms` gates for the Makkai/Forest word-problem route to normalization
(Path B, polycell.md §2.3 / §3.9) — the SN/decidability cross-check leg.  Currently covers the
dimension-1 free-monoid structure on ωcE scaffold words (`WordFreeMonoid.lean`): the arena Makkai's
word-equality recursion is based at.

Lean per-decl gates only — no namespace sweep, no dependency walk (see `AuditAll` exclusion note).
-/

-- DIMENSION-1 FREE MONOID (one-object free category) on ωcE words — the Makkai word-problem arena.
-- Words under concatenation form a monoid (associativity + two-sided identity); suspension and the
-- word-code serialization are monoid homomorphisms.  The recursion base of Makkai's algorithm; the actual
-- word equality modulo rewriting + the termination/confluence (= SN) of the FX presentation are the body
-- of Path B still owed.  All proved propext-free (manual list inductions, not core List.append_assoc).
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.append_assoc
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.empty_append
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.append_empty
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.suspend_empty
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.suspend_append
#assert_no_axioms FX1Poly.OmegacE.OmegacEWordCode.append_assoc
#assert_no_axioms FX1Poly.OmegacE.OmegacEWordCode.empty_append
#assert_no_axioms FX1Poly.OmegacE.OmegacEWordCode.append_empty
#assert_no_axioms FX1Poly.OmegacE.OmegacEWordCode.ofWord_empty
#assert_no_axioms FX1Poly.OmegacE.OmegacEWordCode.toWord_empty

-- FREE-MONOID UNIVERSAL PROPERTY: OmegacEWord is the FREE monoid on its generators — for any target monoid
-- (explicit multiply/unit + laws) and generator interpretation, foldOut is the unique extending monoid
-- homomorphism.  The categorical "free" characterization (how to map OUT of the free structure), the basis
-- for any future word-problem decision/normal-form target.  All zero-axiom (List.foldr + structural list
-- inductions; the dim-2 rewriting relations that make word equality non-trivial are the next Path-B step).
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.foldOut_empty
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.foldOut_append
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.foldOut_singleton
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.foldOut_unique

-- UNIVERSAL-PROPERTY CONSEQUENCES: hom_ext (two monoid homs out of the free monoid agreeing on generators
-- are equal — uniqueness packaged for direct use) and length_eq_foldOut (word length IS the canonical free-
-- monoid hom into (ℕ,+,0) sending each generator to 1 — the textbook universal-property instance).
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.hom_ext
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.length_eq_foldOut

-- DIMENSION-2 WORD REWRITING (Rewrite.lean): word equality MODULO a rule system — the structure whose
-- convergence (termination + confluence) is the Makkai word-problem decision. One-step rewriting fires a
-- rule inside any context (congruence by construction); many-step is its reflexive-transitive closure.
-- First invariant: length is preserved under a length-preserving system (one-step + many-step). Plus the
-- algebraic package: many-step is reflexive/transitive + a two-sided append-congruence (monoid-compatible
-- preorder). Honest scope: the rewriting SUBSTRATE — NOT yet the FX-Step bridge, confluence, or decidability.
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
