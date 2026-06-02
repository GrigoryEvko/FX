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
import FX1Poly.OmegacE.TranspositionSystem
import FX1Poly.OmegacE.TranspositionConfluence
import FX1Poly.OmegacE.TranspositionReducer
import FX1Poly.OmegacE.AbsorptionSystem
import FX1Poly.OmegacE.AbsorptionConfluence
import FX1Poly.OmegacE.AbsorptionLocalConfluence
import FX1Poly.OmegacE.AbsorptionReducer
import FX1Poly.OmegacE.SortingSystem
import FX1Poly.OmegacE.SortingTermination
import FX1Poly.OmegacE.SortingConfluence
import FX1Poly.OmegacE.SortingReducer

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

-- IDEMPOTENT LOCAL CONFLUENCE + DECIDABILITY (IdempotentConfluence.lean): the capstone — the FIRST non-trivial
-- FULLY-DECIDED ωcE system. listPrefixSplit (overlap combinatorial core) + joinableWhenLeftShorter (the 3
-- overlap cases: []/[c] collapse to equal reducts, c::c::mid' is the disjoint commuting case) ⟹
-- idempotentHasLocalConfluence (trichotomy on redex positions) ⟹ decidableConvertibleModulo_idempotentSystem
-- (via decidableConvertibleModulo_ofConvergent: local confluence + shipped termination + shipped reducer).
-- PROPEXT DISCIPLINE: simp (even simp only with clean lemmas) pulls propext — ALL list reasoning is rw-only,
-- via singleConsAppend/doubleConsAppend (rfl redex-collapsers, also avoiding injection's [].append artifacts)
-- + listAppendNil + explicit-arg listAppendAssoc. Validates newman + the convergent-presentation decision
-- end-to-end on a real genuinely-rewriting presentation (the empty system was vacuous).
#assert_no_axioms FX1Poly.OmegacE.listAppendNil
#assert_no_axioms FX1Poly.OmegacE.singleConsAppend
#assert_no_axioms FX1Poly.OmegacE.doubleConsAppend
#assert_no_axioms FX1Poly.OmegacE.listPrefixSplit
#assert_no_axioms FX1Poly.OmegacE.joinable_of_wordEq
#assert_no_axioms FX1Poly.OmegacE.joinableWhenLeftShorter
#assert_no_axioms FX1Poly.OmegacE.idempotentHasLocalConfluence
#assert_no_axioms FX1Poly.OmegacE.decidableConvertibleModulo_idempotentSystem

-- FIRST CONCRETE LENGTH-PRESERVING PRESENTATION (TranspositionSystem.lean): the adjacent-transposition rule
-- [a,b] → [b,a], the complement of the length-REDUCING idempotent system. The first system in the
-- length-PRESERVING class (IsLengthPreservingSystem) — the simplest convergent class for which length is NOT a
-- termination measure (decided by bounded search over the finite same-length word set). transpositionRule_fires
-- is the non-vacuity witness; transpositionSystem_isLengthPreserving is the headline certificate; the three
-- length-invariance corollaries (one-step / many-step / convertibility) instantiate the shipped preservation
-- lemmas and establish that the whole reduction/convertibility graph of a word stays within fixed length (the
-- bounded-search-decidability substrate). Honest scope: SYSTEM + length invariants + non-vacuity only;
-- termination (inversion measure, needs a ≠ b), orthogonal local confluence, and the bounded-search decision
-- are the deferred subsequent atoms (SN-118 continuation).
#assert_no_axioms FX1Poly.OmegacE.transpositionRule
#assert_no_axioms FX1Poly.OmegacE.transpositionSystem
#assert_no_axioms FX1Poly.OmegacE.transpositionRule_fires
#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_isLengthPreserving
#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_rewritesOneStep_length_preserved
#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_rewritesMany_length_preserved
#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_convertibleModulo_length_preserved

-- TRANSPOSITION TERMINATION MEASURE (TranspositionSystem.lean): the inversion-count measure infrastructure
-- toward SN-118 termination. The system is length-PRESERVING, so length is no measure; the inversion count
-- (firstCell-before-secondCell ordered pairs) strictly decreases per swap. countOccurrences + aBeforeBInversions
-- are the measure; the two append-homomorphism lemmas (countOccurrences_append, aBeforeBInversions_append with
-- its cross-term count-product) are the reusable core the strict-decrease proof's context cases consume. The
-- strict-decrease lemma + IsTerminating assembly are the next increment. ZERO-AXIOM DISCIPLINE: aBeforeBInversions_append
-- avoids Nat.add_mul (leaks propext) via Nat.add_comm 1 _ + Nat.succ_mul, and avoids ac_rfl (leaks propext +
-- Quot.sound) via explicit Nat.add_assoc/add_left_comm canonicalization.
#assert_no_axioms FX1Poly.OmegacE.countOccurrences
#assert_no_axioms FX1Poly.OmegacE.aBeforeBInversions
#assert_no_axioms FX1Poly.OmegacE.countOccurrences_append
#assert_no_axioms FX1Poly.OmegacE.aBeforeBInversions_append

-- TRANSPOSITION TERMINATION COMPLETE (TranspositionSystem.lean): the SN-118 termination half. The inversion
-- measure decreases per swap, so the length-PRESERVING transposition system is terminating — the genuine
-- NON-length certificate (complement of the idempotent system's length-reducing one). countOccurrences_preserved_by_step
-- (multiset invariance) → aBeforeBInversions_decreases (strict decrease, needs firstCell ≠ secondCell) →
-- transpositionSystem_isTerminating (Subrelation into InvImage (·<·) measure, mirroring IsTerminating_of_lengthReducing).
-- All zero-axiom (the if-residual base cases close by default-transparency rfl; no Nat.add_mul / ac_rfl). Remaining
-- SN-118 atoms: orthogonal local confluence + bounded-search decidability.
#assert_no_axioms FX1Poly.OmegacE.countOccurrences_preserved_by_step
#assert_no_axioms FX1Poly.OmegacE.aBeforeBInversions_decreases
#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_isTerminating

-- TRANSPOSITION CONFLUENCE (TranspositionConfluence.lean): the SN-118 convergence half. The single rule
-- [a,b]→[b,a] has NO self-overlap (overlap would force a=b), so it is ORTHOGONAL — the prefix-trichotomy's
-- one-cell-overlap case is VACUOUS (absurd … distinct), unlike idempotent's real [c,c,c] critical pair.
-- transpositionRewriteOneStep_decomposition/ofDecomposition (structural inversion) → transpositionJoinableWhenLeftShorter
-- (disjoint redexes commute) → transpositionHasLocalConfluence → transpositionHasConfluence (newman + the shipped
-- termination). Generic word-list helpers reused from IdempotentConfluence; disjoint-case word equalities via
-- explicit-arg rw chains (simp only pulls propext from its machinery). All zero-axiom. Remaining SN-118 atom:
-- a WordReducer for the decidable word problem.
#assert_no_axioms FX1Poly.OmegacE.transpositionRewriteOneStep_decomposition
#assert_no_axioms FX1Poly.OmegacE.transpositionRewriteOneStep_ofDecomposition
#assert_no_axioms FX1Poly.OmegacE.transpositionJoinableWhenLeftShorter
#assert_no_axioms FX1Poly.OmegacE.transpositionHasLocalConfluence
#assert_no_axioms FX1Poly.OmegacE.transpositionHasConfluence

-- TRANSPOSITION REDUCER + DECIDABLE WORD PROBLEM (TranspositionReducer.lean): the SN-118 FINAL atom (#621) —
-- bounded-search decidability for the length-PRESERVING swap system, mirroring the idempotent reducer with a
-- length-preserving rule. transpositionReduceCells (leftmost-[a,b] scan, splice to [b,a]) with soundness (a
-- splice IS a RewritesOneStep via transpositionRule_fires under context) and completeness (transpositionRewrite_
-- implies_reduceCells_isSome: every step means the scan finds a redex, via the two append-monotonicity lemmas).
-- transpositionWordReducer bundles them (NO distinctness needed — sound/complete hold even at a=b); then
-- decidableConvertibleModulo_transpositionSystem = decidableConvertibleModulo_ofConvergent fed the orthogonal
-- local confluence + the inversion-measure termination (needs a≠b) + this reducer = the FIRST fully-decided
-- length-PRESERVING ωcE system (genuine Newman, length is no measure), CLOSING SN-118. The generic option_isSome_map
-- is reused from IdempotentReducer. propext-clean: nomatch/Bool.noConfusion (not simp-to-True), dsimp+if_pos⟨rfl,rfl⟩,
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

-- ABSORPTION SYSTEM — FIRST TWO-RULE / INTER-RULE CRITICAL PAIR (AbsorptionSystem.lean): SN-119 (#622) opener.
-- A survivingCell absorbs an adjacent vanishingCell on either side: TWO rules [v,s]→[s,s] and [s,v]→[s,s].
-- The genuinely new content vs the single-rule predecessors: membership is a DISJUNCTION, so every `fire`
-- inversion `rcases`-es which rule fired. Length-PRESERVING (keeps SN-118's achievement), so length is no
-- measure; terminating by countOccurrences vanishingCell strict decrease (each rule absorbs one v) — a SIMPLER
-- measure than SN-118's inversion count (no cross term), REUSING the shipped countOccurrences + _append. Needs
-- v≠s (at v=s both rules are self-loops). Zero-axiom: fire witnesses Or.inl/Or.inr rfl; isLengthPreserving =
-- rcases + 2 rfl; decrease by induction (fire rcases → both 0<1; context = append-split + Nat.add_lt_add_*);
-- isTerminating = Subrelation into InvImage (·<·) measure. The one propext trap (rw [if_pos rfl] leaving
-- 1 + countOccurrences _ [] = 1) closed by explicit default-transparency rfl. Deferred SN-119 atoms: the genuine
-- inter-rule LOCAL CONFLUENCE (real critical pairs [v,s,v]/[s,v,s] joining to [s,s,s], NOT vacuous) + the
-- two-rule WordReducer decidability.
#assert_no_axioms FX1Poly.OmegacE.absorptionRuleVanishingLeft
#assert_no_axioms FX1Poly.OmegacE.absorptionRuleVanishingRight
#assert_no_axioms FX1Poly.OmegacE.absorptionSystem
#assert_no_axioms FX1Poly.OmegacE.absorptionRuleVanishingLeft_fires
#assert_no_axioms FX1Poly.OmegacE.absorptionRuleVanishingRight_fires
#assert_no_axioms FX1Poly.OmegacE.absorptionSystem_isLengthPreserving
#assert_no_axioms FX1Poly.OmegacE.absorptionSystem_rewritesOneStep_length_preserved
#assert_no_axioms FX1Poly.OmegacE.absorptionSystem_rewritesMany_length_preserved
#assert_no_axioms FX1Poly.OmegacE.absorptionSystem_convertibleModulo_length_preserved
#assert_no_axioms FX1Poly.OmegacE.vanishingCount_decreases_by_step
#assert_no_axioms FX1Poly.OmegacE.absorptionSystem_isTerminating

-- ABSORPTION DECOMPOSITION — STRUCTURAL INVERSION (AbsorptionConfluence.lean): SN-119 progress 2a. A step IS
-- "rewrite a mixed pair to [s,s] in context"; the inversion carries a DISJUNCTION on the source redex shape
-- ([v,s] OR [s,v]) — the new structure vs transposition's single-rule decomposition. _decomposition (forward,
-- induction on the step; fire rcases-es the rule disjunction, context cases reuse listAppendAssoc) +
-- _ofDecompositionLeft/Right (backward, fire under both contexts, one per rule). The critical-pair-extraction
-- tools the local-confluence proof (next increment) consumes. Zero-axiom: pure listAppendAssoc rw chains, no
-- simp. Deferred: the genuine inter-rule LOCAL CONFLUENCE (real [v,s,v] multi-step join to [s,s,s]) + newman
-- + the two-rule WordReducer decidability.
#assert_no_axioms FX1Poly.OmegacE.absorptionRewriteOneStep_decomposition
#assert_no_axioms FX1Poly.OmegacE.absorptionRewriteOneStep_ofDecompositionLeft
#assert_no_axioms FX1Poly.OmegacE.absorptionRewriteOneStep_ofDecompositionRight

-- ABSORPTION CRITICAL-PAIR JOIN (AbsorptionConfluence.lean): SN-119 progress 2b-i — the mathematical HEART.
-- The genuine inter-rule critical pair: the overlap word [v,s,v] has two one-step reducts [s,s,v] (rule-Left at
-- front) and [v,s,s] (rule-Right at back), both reducing in ONE further step to the common all-surviving [s,s,s]
-- ([s,s,v] fires rule-Right on its [s,v] suffix; [v,s,s] fires rule-Left on its [v,s] prefix). NOT vacuous (unlike
-- transposition's overlap which forced a=b) and NOT trivially-equal (unlike idempotent [c,c,c]) — the genuinely-new
-- multi-step join SN-119 contributes. tripleConsAppend = length-3 cons-collapse (rfl) for the 3-cell words.
-- Zero-axiom: explicit listAppendAssoc/singleConsAppend/doubleConsAppend/tripleConsAppend rw chains (no simp).
-- Deferred (progress 2b-ii): the full absorptionHasLocalConfluence (4-combo wrapper consuming THIS lemma in the
-- (Left,Right) overlap case + the trivial [s,v,s] + matched-vacuous + disjoint-commute) + newman ⟹ confluence.
#assert_no_axioms FX1Poly.OmegacE.tripleConsAppend
#assert_no_axioms FX1Poly.OmegacE.absorptionCriticalPairJoinLeftRight

-- ABSORPTION DISJOINT-COMMUTE (AbsorptionConfluence.lean): SN-119 progress 2b-ii first piece — the third
-- trichotomy branch (the bulk). Two non-overlapping redexes commute: firing pairA→[s,s] and pairB→[s,s] both
-- reach the common all-[s,s] word. KEY ECONOMY: the word equalities are PURE associativity (pairs stay opaque
-- as ++pairA/++pairB, never cons-collapsed), so this ONE helper covers all four rule combinations — the rule
-- disjunction is consumed only at the two _ofDecomposition fires (rcases hPairA/hPairB → Left/Right). Zero-axiom
-- (explicit listAppendAssoc rw chains, no simp). Deferred: the absorptionHasLocalConfluence wrapper (listPrefixSplit
-- trichotomy dispatching same-position/critical-pair/THIS disjoint) + newman ⟹ absorptionHasConfluence.
#assert_no_axioms FX1Poly.OmegacE.absorptionJoinableDisjoint

-- ABSORPTION LOCAL + GLOBAL CONFLUENCE (AbsorptionLocalConfluence.lean): SN-119 progress 2b-ii(b) — the
-- confluence capstone, assembled from the AbsorptionConfluence building blocks. absorptionJoinableWhenLeftShorter
-- (4 rule combos × listPrefixSplit trichotomy: nil same-position matched=equal/mismatched=v≠s absurd; [m] one-cell
-- overlap (L,R)=[v,s,v] critical-pair lemma / (R,L)=[s,v,s] both reducts [s,s,s] / matched absurd; cons-cons disjoint
-- = the commute helper) → absorptionHasLocalConfluence (decompose both reducts, Nat.le_total dispatches 8 leaves) →
-- absorptionHasConfluence (newman + the shipped termination) = the FIRST fully-CONFLUENT two-rule presentation with
-- genuine inter-rule critical pairs. Zero-axiom: disjoint leaves bridge cons-form↔append-form via ←doubleConsAppend +
-- ←listAppendAssoc (no simp). Only the decidable word problem (two-rule WordReducer, progress 3) remains to close SN-119.
#assert_no_axioms FX1Poly.OmegacE.absorptionJoinableWhenLeftShorter
#assert_no_axioms FX1Poly.OmegacE.absorptionHasLocalConfluence
#assert_no_axioms FX1Poly.OmegacE.absorptionHasConfluence

-- ABSORPTION REDUCER + DECIDABLE WORD PROBLEM (AbsorptionReducer.lean): the SN-119 CAPSTONE (#622) — CLOSES SN-119.
-- A two-rule WordReducer with a SINGLE disjunction-if scanner (both rules splice a mixed pair to [s,s], so
-- (first=v ∧ second=s) ∨ (first=s ∧ second=v) covers both). firesLeft/firesRight (Or.inl/Or.inr, NO distinctness —
-- both branches → [s,s]); monotonicity (reuse option_isSome_map); sound (fire case rcases the disjunction CONDITION
-- → rule-Left/Right); complete (absorptionRewrite_implies_reduceCells_isSome: fire case rcases the rule DISJUNCTION).
-- absorptionWordReducer bundles them (NO distinctness); decidableConvertibleModulo_absorptionSystem =
-- decidableConvertibleModulo_ofConvergent fed absorptionHasLocalConfluence + absorptionSystem_isTerminating (needs
-- v≠s) + the reducer = the FIRST FULLY-DECIDED two-rule presentation with genuine inter-rule critical pairs.
-- Faithful mirror of the gated TranspositionReducer with the two-rule disjunction-if; all zero-axiom. SN-119 CLOSED.
#assert_no_axioms FX1Poly.OmegacE.absorptionReduceCells
#assert_no_axioms FX1Poly.OmegacE.absorptionReduceCells_firesLeft
#assert_no_axioms FX1Poly.OmegacE.absorptionReduceCells_firesRight
#assert_no_axioms FX1Poly.OmegacE.absorptionReduceCells_isSome_append_right
#assert_no_axioms FX1Poly.OmegacE.absorptionReduceCells_isSome_append_left
#assert_no_axioms FX1Poly.OmegacE.absorptionReduceCells_sound
#assert_no_axioms FX1Poly.OmegacE.absorptionRewrite_implies_reduceCells_isSome
#assert_no_axioms FX1Poly.OmegacE.absorptionReduceOnce
#assert_no_axioms FX1Poly.OmegacE.absorptionWordReducer
#assert_no_axioms FX1Poly.OmegacE.decidableConvertibleModulo_absorptionSystem

-- SORTING / SYMMETRIC SYSTEM — GUARDED RULE FAMILY (SortingSystem.lean): SN-120 opener (#623), the "graduation".
-- Parameterized by a priority slotValue : OmegacECell → Nat; the rule [a,b]→[b,a] fires for EVERY descending pair
-- (slotValue b < slotValue a) — bubble sort = the symmetric-group word problem. Membership is an EXISTENTIAL with a
-- strict-order GUARD (∃ a b, slotValue b < slotValue a ∧ rule = sortingSwapRule a b) — the genuinely-new structure
-- vs the absorption system's two-element disjunction. fires = guarded fire (⟨a,b,descending,rfl⟩); isLengthPreserving
-- = obtain the existential + rfl; the 3 length invariants instantiate the shipped preservation lemmas. Zero-axiom.
-- Deferred SN-120 atoms: INVERSION-count termination (all out-of-order pairs, generalizing SN-118's aBeforeBInversions);
-- LOCAL CONFLUENCE with the braid critical pair [a,b,c] (slotValue a>b>c; reducts join to sorted [c,b,a] via multi-step);
-- a guarded WordReducer + decidability.
#assert_no_axioms FX1Poly.OmegacE.sortingSwapRule
#assert_no_axioms FX1Poly.OmegacE.sortingSystem
#assert_no_axioms FX1Poly.OmegacE.sortingSwapRule_fires
#assert_no_axioms FX1Poly.OmegacE.sortingSystem_isLengthPreserving
#assert_no_axioms FX1Poly.OmegacE.sortingSystem_rewritesOneStep_length_preserved
#assert_no_axioms FX1Poly.OmegacE.sortingSystem_rewritesMany_length_preserved
#assert_no_axioms FX1Poly.OmegacE.sortingSystem_convertibleModulo_length_preserved

-- SORTING INVERSION MEASURE (SortingTermination.lean): SN-120 progress 2a — the bubble-sort termination measure.
-- countBelowThreshold (count cells with slotValue < threshold) + countInversions (total out-of-order pairs) +
-- crossInversionCount (the SUM-fold cross term across an append). The two append homomorphisms are the reusable core;
-- countInversions_append's cons case is a five-term Nat AC rearrangement (a+b)+((c+d)+e)=((a+c)+d)+(b+e), discharged by
-- explicit Nat.add_assoc/add_left_comm normalizing both sides to a+(b+(c+(d+e))) — NOT ac_rfl (leaks propext+Quot.sound),
-- the heavier analogue of SN-118's aBeforeBInversions (whose cross term was a single product). Zero-axiom.
#assert_no_axioms FX1Poly.OmegacE.countBelowThreshold
#assert_no_axioms FX1Poly.OmegacE.countInversions
#assert_no_axioms FX1Poly.OmegacE.crossInversionCount
#assert_no_axioms FX1Poly.OmegacE.countBelowThreshold_append
#assert_no_axioms FX1Poly.OmegacE.countInversions_append

-- SORTING TERMINATION (SortingTermination.lean): SN-120 progress 2b — the bubble-sort termination proper.
-- Multiset invariance (countBelowThreshold preserved by a swap) lifts to cross-term preservation in BOTH arguments
-- of crossInversionCount (via the additive crossInversionCount_append_left), so the countInversions_append context
-- cases keep the cross term fixed and the strict decrease (fire: inner measure 1->0 by <-asymmetry) rides the inner
-- IH. sortingSystem_isTerminating embeds reduction into InvImage (· < ·) countInversions — and unlike the
-- transposition system needs NO external a≠b, since the strict-order guard is baked into sortingSystem membership.
-- Zero-axiom (if_neg/if_pos + Nat.add_comm/add_zero/add_assoc + Nat.lt_asymm + Subrelation.accessible/InvImage.wf).
#assert_no_axioms FX1Poly.OmegacE.countBelowThreshold_preserved_by_step
#assert_no_axioms FX1Poly.OmegacE.crossInversionCount_append_left
#assert_no_axioms FX1Poly.OmegacE.crossInversionCount_preserved_right_by_step
#assert_no_axioms FX1Poly.OmegacE.crossInversionCount_preserved_left_by_step
#assert_no_axioms FX1Poly.OmegacE.countInversions_decreases
#assert_no_axioms FX1Poly.OmegacE.sortingSystem_isTerminating

-- SORTING CONFLUENCE (SortingConfluence.lean): SN-120 progress 3 — structural inversion + the BRAID critical pair.
-- decomposition/ofDecomposition mirror the transposition twins but EXISTENTIALLY produce the swapped cells + guard
-- (the rule is a guarded family, not a fixed pair). sortingBraidCriticalPairJoinBare is the mathematical heart: for
-- a strictly descending triple slotValue c < slotValue b < slotValue a, the front reduct [b,a,c] and back reduct
-- [a,c,b] of [a,b,c] both reach the sorted [c,b,a] in TWO steps each — the braid relation aba=bab, the first true
-- multi-step RewritesMany join. The four ofDecomposition steps typecheck against the concrete triples by defeq (the
-- list appends compute), so no word massaging at the bare layer. Zero-axiom (Nat.lt_trans + RewritesMany.step/single).
#assert_no_axioms FX1Poly.OmegacE.sortingRewriteOneStep_decomposition
#assert_no_axioms FX1Poly.OmegacE.sortingRewriteOneStep_ofDecomposition
#assert_no_axioms FX1Poly.OmegacE.sortingBraidCriticalPairJoinBare

-- Joinable.inContext is generic (any system): lift a bare ⟨bareLeft⟩⋈⟨bareRight⟩ join under leftCtx _ rightCtx via
-- RewritesMany.underRightContext/underLeftContext + one listAppendAssoc reassociation (append IS ++ on cells, so the
-- rest is defeq). sortingBraidCriticalPairJoin is the bare braid join lifted to context — the exact shape the
-- one-cell-overlap (braid) case of local confluence needs. Zero-axiom.
#assert_no_axioms FX1Poly.OmegacE.OmegacEWord.Joinable.inContext
#assert_no_axioms FX1Poly.OmegacE.sortingBraidCriticalPairJoin

-- SORTING LOCAL + GLOBAL CONFLUENCE (SortingConfluence.lean): SN-120 confluence headline. The prefix-split
-- trichotomy joinableWhenLeftShorter dispatches: nil = equal reducts (NOT a mismatch — both redexes coincide);
-- single = THE braid critical pair (reuses sortingBraidCriticalPairJoin, the new content vs transposition's vacuous
-- one-cell case); cons-cons = disjoint commute (mirrors transposition/absorption). hasLocalConfluence decomposes both
-- reducts + Nat.le_total dispatch; hasConfluence = newman localConfluence + sortingSystem_isTerminating (the guarded
-- family needs no external a≠b). The braid word-eqs close by listAppendAssoc reassociation + a default-transparency
-- rfl (the inner concrete-prefix appends are defeq). The sorting/symmetric presentation is now CONVERGENT. Zero-axiom.
#assert_no_axioms FX1Poly.OmegacE.sortingJoinableWhenLeftShorter
#assert_no_axioms FX1Poly.OmegacE.sortingHasLocalConfluence
#assert_no_axioms FX1Poly.OmegacE.sortingHasConfluence

-- SORTING REDUCER + DECIDABILITY (SortingReducer.lean): SN-120 CAPSTONE. The bounded-search reducer mirrors the
-- transposition reducer but the scanner's firing test is the DECIDABLE ORDER GUARD slotValue second < slotValue
-- first (Nat.decLt), not a fixed-pair cell equality. soundness fires sortingSwapRule_fires under context;
-- completeness destructures the guarded existential membership. decidableConvertibleModulo_sortingSystem =
-- decidableConvertibleModulo_ofConvergent (sortingHasLocalConfluence + sortingSystem_isTerminating + reducer) needs
-- NO distinctness (the guard is in membership). Third fully-decided OmegacE system, the symmetric-group word problem.
-- Zero-axiom (nomatch/Bool.noConfusion, dsimp+if_pos, option_isSome_map reused; no list-append simp).
#assert_no_axioms FX1Poly.OmegacE.sortingReduceCells_fires
#assert_no_axioms FX1Poly.OmegacE.sortingReduceCells_isSome_append_right
#assert_no_axioms FX1Poly.OmegacE.sortingReduceCells_isSome_append_left
#assert_no_axioms FX1Poly.OmegacE.sortingReduceCells_sound
#assert_no_axioms FX1Poly.OmegacE.sortingRewrite_implies_reduceCells_isSome
#assert_no_axioms FX1Poly.OmegacE.sortingWordReducer
#assert_no_axioms FX1Poly.OmegacE.decidableConvertibleModulo_sortingSystem
