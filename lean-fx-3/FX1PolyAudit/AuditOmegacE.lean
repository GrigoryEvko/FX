import FX1PolyAudit.DependencyAudit
import FX1Poly.OmegacE.WordFreeMonoid
import FX1Poly.OmegacE.WordFreeMonoidUniversal
import FX1Poly.OmegacE.Rewrite
import FX1Poly.OmegacE.Confluence
import FX1Poly.OmegacE.WordProblem
import FX1Poly.OmegacE.ReducerNormalizer
import FX1Poly.OmegacE.EmptySystem
import FX1Poly.OmegacE.IdempotentSystem
import FX1Poly.OmegacE.IdempotentReducer
import FX1Poly.OmegacE.IdempotentConfluence

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

-- CONFLUENCE / CHURCH-ROSSER (Confluence.lean): the decidability enabler. Joinable (∃ common reduct) is
-- reflexive/symmetric, contains RewritesMany, embeds into ConvertibleModulo, preserves length. The standard
-- metatheorem churchRosser_of_confluence (confluence ⟹ Church-Rosser, trans case merges common reducts via
-- the diamond) + convertibleModulo_iff_joinable_of_churchRosser (under CR, convertible = joinable, reducing
-- the symm-trans closure to a searchable ∃). HasConfluence/HasChurchRosser are PROPERTIES (discharged per
-- concrete system later); decidability additionally needs a terminating normalizer — both subsequent atoms.
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.Joinable.refl
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.Joinable.symm
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.Joinable.ofRewritesMany
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.Joinable.toConvertible
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.Joinable.length_preserved
#assert_no_axioms FX1Poly.OmegacE.HasConfluence
#assert_no_axioms FX1Poly.OmegacE.HasChurchRosser
#assert_no_axioms FX1Poly.OmegacE.churchRosser_of_confluence
#assert_no_axioms FX1Poly.OmegacE.convertibleModulo_iff_joinable_of_churchRosser

-- NEWMAN'S LEMMA (Confluence.lean): confluence from the checkable local confluence. HasLocalConfluence (peak
-- of two single steps joinable — critical-pair-checkable) + IsTerminating (every word Acc under reduction) ⟹
-- HasConfluence (newman), via confluenceFromAccessible (Acc.rec well-founded tiling: local-confluence peak +
-- two strictly-smaller IH applications). THE tool to discharge HasConfluence on a concrete system; with
-- churchRosser_of_confluence + WordProblem's decision, a terminating locally-confluent system has a decidable
-- word problem. Acc.rec is propext-free here (constant-shaped motive).
#assert_no_axioms FX1Poly.OmegacE.HasLocalConfluence
#assert_no_axioms FX1Poly.OmegacE.IsTerminating
#assert_no_axioms FX1Poly.OmegacE.confluenceFromAccessible
#assert_no_axioms FX1Poly.OmegacE.newman

-- TERMINATION FROM A LENGTH MEASURE (Confluence.lean): IsLengthReducingSystem (every rule strictly shortens)
-- ⟹ IsTerminating (IsTerminating_of_lengthReducing), via length_lt_of_lengthReducing (one step strictly
-- decreases length) + Subrelation.accessible into InvImage (·<·) length (Nat.lt well-founded). Discharges the
-- termination hypothesis of the convergent-presentation decision from a CHECKABLE measure — with newman, a
-- concrete length-reducing system needs only local confluence + a reducer.
#assert_no_axioms FX1Poly.OmegacE.IsLengthReducingSystem
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.RewritesOneStep.length_lt_of_lengthReducing
#assert_no_axioms FX1Poly.OmegacE.IsTerminating_of_lengthReducing

-- WORD PROBLEM DECIDED (WordProblem.lean): convergent presentation ⟹ decidable convertibility — the Path-B
-- twin of Conv.decidableOfStronglyNormalizing. WordNormalizer (normalize to a reachable normal form) +
-- rigidity (rewritesMany_eq_of_blocksStep) give Joinable = NF-equality, then Church-Rosser gives
-- ConvertibleModulo = NF-equality, hence Decidable (ConvertibleModulo) by decidable_of_iff over the
-- propext-free word DecidableEq. CONDITIONAL on HasConfluence + a WordNormalizer (discharged per concrete
-- system later); the convertibility characterization uses Iff.trans, NOT rw [← iff] (which pulls propext).
#assert_no_axioms FX1Poly.OmegacE.WordNormalizer
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.rewritesMany_eq_of_blocksStep
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.Joinable.iff_normalize_eq
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.ConvertibleModulo.iff_normalize_eq
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.ConvertibleModulo.decidableOfNormalizer

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

-- FIRST CONCRETE CONVERGENT PRESENTATION (EmptySystem.lean): the empty (free-monoid) rule system discharges
-- BOTH abstract hypotheses end-to-end — no word rewrites (rewritesOneStep_emptySystem_absurd), identity
-- normalizer (emptyWordNormalizer), vacuous confluence (emptyHasConfluence) — so its word problem is
-- decidable AND is exactly SYNTACTIC EQUALITY (convertibleModulo_emptySystem_iff_eq), reconnecting dim-2
-- convertibility to dim-1 free-monoid equality. The dim-2 analog of the closed-SN smoke corpus: proof the
-- abstract machinery is non-vacuous. Next concrete atom = a non-trivial length-reducing system.
#assert_no_axioms FX1Poly.OmegacE.emptyRewriteSystem
#assert_no_axioms FX1Poly.OmegacE.rewritesOneStep_emptySystem_absurd
#assert_no_axioms FX1Poly.OmegacE.emptyWordNormalizer
#assert_no_axioms FX1Poly.OmegacE.emptyHasConfluence
#assert_no_axioms FX1Poly.OmegacE.convertibleModulo_emptySystem_iff_eq
#assert_no_axioms FX1Poly.OmegacE.decidableConvertibleModulo_emptySystem

-- FIRST CONCRETE NON-EMPTY TERMINATING PRESENTATION (IdempotentSystem.lean): the idempotent rule [c,c] → [c],
-- the EmptySystem successor its docstring named ("a non-trivial length-reducing system"). Unlike the empty
-- system (which rewrites NOTHING), this one genuinely FIRES (idempotentRule_fires — the non-vacuity witness
-- contrasting rewritesOneStep_emptySystem_absurd) and is the first NON-trivial discharge of IsTerminating
-- (idempotentSystem_isTerminating, via the length measure 1 < 2). Honest scope: termination + non-vacuity only;
-- the full decidable word problem additionally needs a WordReducer (rule-matching reduceOnce) and
-- HasLocalConfluence (critical pair [c,c,c] joins at [c,c] both ways) — the next two Path-B atoms.
#assert_no_axioms FX1Poly.OmegacE.idempotentRule
#assert_no_axioms FX1Poly.OmegacE.idempotentSystem
#assert_no_axioms FX1Poly.OmegacE.idempotentRule_fires
#assert_no_axioms FX1Poly.OmegacE.idempotentSystem_isLengthReducing
#assert_no_axioms FX1Poly.OmegacE.idempotentSystem_isTerminating

-- IDEMPOTENT REDUCER + TERMINATING NORMALIZER (IdempotentReducer.lean): the searchable engine the idempotent
-- system supplies — idempotentReduceCells (leftmost-redex scan, splice [c,c]→[c]) with soundness (a splice IS
-- a RewritesOneStep via idempotentRule_fires under context) and completeness (idempotentRewrite_implies_
-- reduceCells_isSome: every one-step rewrite means the scan finds a redex, via the append-monotonicity lemmas
-- = the structural inversion of one-step rewriting). idempotentWordReducer bundles them (the FIRST concrete
-- WordReducer that genuinely rewrites — the empty system's was the identity); idempotentWordNormalizer =
-- toNormalizer along the shipped termination = the FIRST terminating normalizer for a non-trivial concrete
-- ωcE system. Honest scope: decidability still needs HasLocalConfluence (the [c,c,c] critical pair) — the
-- final Path-B atom for this system. propext-clean: nomatch/Bool.noConfusion (not simp-to-True), dsimp+if_pos.
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

-- IDEMPOTENT CONFLUENCE LAYER — STRUCTURAL CHARACTERIZATION (IdempotentConfluence.lean): one-step idempotent
-- rewriting IS "collapse one [c,c] to [c] in context" — rewriteOneStep_decomposition (forward: induction on
-- the rewrite, context ctors extend A/B) + rewriteOneStep_ofDecomposition (backward: fire under both contexts).
-- The inversion that turns the inductive RewritesOneStep into an explicit redex position = the critical-pair
-- extraction tool local confluence consumes. listAppendAssoc = propext-free append associativity (core
-- List.append_assoc carries propext — the Word.lean discipline). Honest scope: characterization only;
-- HasLocalConfluence (the [c,c,c] overlap analysis) + decidability are the next atom.
#assert_no_axioms FX1Poly.OmegacE.listAppendAssoc
#assert_no_axioms FX1Poly.OmegacE.rewriteOneStep_decomposition
#assert_no_axioms FX1Poly.OmegacE.rewriteOneStep_ofDecomposition
