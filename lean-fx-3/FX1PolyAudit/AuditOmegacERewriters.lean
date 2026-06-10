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
import FX1Poly.OmegacE.OmegacEFiniteType

/-! # FX1PolyAudit/AuditOmegacERewriters — omega-cE-layer zero-axiom gates, shard 02 of 2 (split from the AuditOmegacE monolith for parallel gate elaboration).  Covers the length-preserving presentations (adjacent transposition, two-rule absorption, guarded sorting/symmetric) with their termination measures, critical-pair joins, local + global confluence, reducers + decidability, and the ωcE binary finite-type generator family. -/

-- FIRST CONCRETE LENGTH-PRESERVING PRESENTATION (TranspositionSystem.lean): the adjacent-transposition rule
-- [a,b] → [b,a], the complement of the length-REDUCING idempotent system. The first system in the
-- length-PRESERVING class (IsLengthPreservingSystem) — the simplest convergent class for which length is NOT a
-- termination measure (decided by bounded search over the finite same-length word set). transpositionRule_fires
-- is the non-vacuity witness; transpositionSystem_isLengthPreserving is the headline certificate; the three
-- length-invariance corollaries (one-step / many-step / convertibility) instantiate the shipped preservation
-- lemmas and establish that the whole reduction/convertibility graph of a word stays within fixed length (the
-- bounded-search-decidability substrate). Scope: the SYSTEM + length invariants + non-vacuity; termination
-- (inversion measure, needs a ≠ b), orthogonal local confluence, and the bounded-search decision are the
-- slices below.
#assert_no_axioms FX1Poly.OmegacE.transpositionRule
#assert_no_axioms FX1Poly.OmegacE.transpositionSystem
#assert_no_axioms FX1Poly.OmegacE.transpositionRule_fires
#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_isLengthPreserving
#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_rewritesOneStep_length_preserved
#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_rewritesMany_length_preserved
#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_convertibleModulo_length_preserved

-- TRANSPOSITION TERMINATION MEASURE (TranspositionSystem.lean): the inversion-count measure infrastructure
-- for the transposition termination proof. The system is length-PRESERVING, so length is no measure; the
-- inversion count (firstCell-before-secondCell ordered pairs) strictly decreases per swap. countOccurrences +
-- aBeforeBInversions are the measure; the two append-homomorphism lemmas (countOccurrences_append,
-- aBeforeBInversions_append with its cross-term count-product) are the reusable core the strict-decrease
-- proof's context cases consume. ZERO-AXIOM DISCIPLINE: aBeforeBInversions_append avoids Nat.add_mul (leaks
-- propext) via Nat.add_comm 1 _ + Nat.succ_mul, and avoids ac_rfl (leaks propext + Quot.sound) via explicit
-- Nat.add_assoc/add_left_comm canonicalization.
#assert_no_axioms FX1Poly.OmegacE.countOccurrences
#assert_no_axioms FX1Poly.OmegacE.aBeforeBInversions
#assert_no_axioms FX1Poly.OmegacE.countOccurrences_append
#assert_no_axioms FX1Poly.OmegacE.aBeforeBInversions_append

-- TRANSPOSITION TERMINATION COMPLETE (TranspositionSystem.lean): the termination proof. The inversion
-- measure decreases per swap, so the length-PRESERVING transposition system is terminating — the genuine
-- NON-length certificate (complement of the idempotent system's length-reducing one). countOccurrences_preserved_by_step
-- (multiset invariance) → aBeforeBInversions_decreases (strict decrease, needs firstCell ≠ secondCell) →
-- transpositionSystem_isTerminating (Subrelation into InvImage (·<·) measure, mirroring IsTerminating_of_lengthReducing).
-- All zero-axiom (the if-residual base cases close by default-transparency rfl; no Nat.add_mul / ac_rfl).
-- Orthogonal local confluence + bounded-search decidability are the slices below.
#assert_no_axioms FX1Poly.OmegacE.countOccurrences_preserved_by_step
#assert_no_axioms FX1Poly.OmegacE.aBeforeBInversions_decreases
#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_isTerminating

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

-- ABSORPTION SYSTEM — FIRST TWO-RULE / INTER-RULE CRITICAL PAIR (AbsorptionSystem.lean).
-- A survivingCell absorbs an adjacent vanishingCell on either side: TWO rules [v,s]→[s,s] and [s,v]→[s,s].
-- The genuinely new content vs the single-rule predecessors: membership is a DISJUNCTION, so every `fire`
-- inversion `rcases`-es which rule fired. Length-PRESERVING (like the transposition system), so length is no
-- measure; terminating by countOccurrences vanishingCell strict decrease (each rule absorbs one v) — a SIMPLER
-- measure than the transposition inversion count (no cross term), REUSING countOccurrences + _append. Needs
-- v≠s (at v=s both rules are self-loops). Zero-axiom: fire witnesses Or.inl/Or.inr rfl; isLengthPreserving =
-- rcases + 2 rfl; decrease by induction (fire rcases → both 0<1; context = append-split + Nat.add_lt_add_*);
-- isTerminating = Subrelation into InvImage (·<·) measure. The one propext trap (rw [if_pos rfl] leaving
-- 1 + countOccurrences _ [] = 1) closed by explicit default-transparency rfl. The genuine inter-rule LOCAL
-- CONFLUENCE (real critical pairs [v,s,v]/[s,v,s] joining to [s,s,s], NOT vacuous) + the two-rule WordReducer
-- decidability are the slices below.
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

-- ABSORPTION DECOMPOSITION — STRUCTURAL INVERSION (AbsorptionConfluence.lean). A step IS
-- "rewrite a mixed pair to [s,s] in context"; the inversion carries a DISJUNCTION on the source redex shape
-- ([v,s] OR [s,v]) — the new structure vs transposition's single-rule decomposition. _decomposition (forward,
-- induction on the step; fire rcases-es the rule disjunction, context cases reuse listAppendAssoc) +
-- _ofDecompositionLeft/Right (backward, fire under both contexts, one per rule). The critical-pair-extraction
-- tools the local-confluence proof consumes. Zero-axiom: pure listAppendAssoc rw chains, no simp. The genuine
-- inter-rule LOCAL CONFLUENCE (real [v,s,v] multi-step join to [s,s,s]) + newman + the two-rule WordReducer
-- decidability are the slices below.
#assert_no_axioms FX1Poly.OmegacE.absorptionRewriteOneStep_decomposition
#assert_no_axioms FX1Poly.OmegacE.absorptionRewriteOneStep_ofDecompositionLeft
#assert_no_axioms FX1Poly.OmegacE.absorptionRewriteOneStep_ofDecompositionRight

-- ABSORPTION CRITICAL-PAIR JOIN (AbsorptionConfluence.lean): the mathematical HEART.
-- The genuine inter-rule critical pair: the overlap word [v,s,v] has two one-step reducts [s,s,v] (rule-Left at
-- front) and [v,s,s] (rule-Right at back), both reducing in ONE further step to the common all-surviving [s,s,s]
-- ([s,s,v] fires rule-Right on its [s,v] suffix; [v,s,s] fires rule-Left on its [v,s] prefix). NOT vacuous (unlike
-- transposition's overlap which forces a=b) and NOT trivially-equal (unlike idempotent [c,c,c]) — a genuine
-- multi-step join. tripleConsAppend = length-3 cons-collapse (rfl) for the 3-cell words.
-- Zero-axiom: explicit listAppendAssoc/singleConsAppend/doubleConsAppend/tripleConsAppend rw chains (no simp).
-- The full absorptionHasLocalConfluence (4-combo wrapper consuming THIS lemma in the (Left,Right) overlap case +
-- the trivial [s,v,s] + matched-vacuous + disjoint-commute) + newman ⟹ confluence is the slice below.
#assert_no_axioms FX1Poly.OmegacE.tripleConsAppend
#assert_no_axioms FX1Poly.OmegacE.absorptionCriticalPairJoinLeftRight

-- ABSORPTION DISJOINT-COMMUTE (AbsorptionConfluence.lean): the third
-- trichotomy branch (the bulk). Two non-overlapping redexes commute: firing pairA→[s,s] and pairB→[s,s] both
-- reach the common all-[s,s] word. KEY ECONOMY: the word equalities are PURE associativity (pairs stay opaque
-- as ++pairA/++pairB, never cons-collapsed), so this ONE helper covers all four rule combinations — the rule
-- disjunction is consumed only at the two _ofDecomposition fires (rcases hPairA/hPairB → Left/Right). Zero-axiom
-- (explicit listAppendAssoc rw chains, no simp). The absorptionHasLocalConfluence wrapper (listPrefixSplit
-- trichotomy dispatching same-position/critical-pair/THIS disjoint) + newman ⟹ absorptionHasConfluence is the
-- slice below.
#assert_no_axioms FX1Poly.OmegacE.absorptionJoinableDisjoint

-- ABSORPTION LOCAL + GLOBAL CONFLUENCE (AbsorptionLocalConfluence.lean): the
-- confluence capstone, assembled from the AbsorptionConfluence building blocks. absorptionJoinableWhenLeftShorter
-- (4 rule combos × listPrefixSplit trichotomy: nil same-position matched=equal/mismatched=v≠s absurd; [m] one-cell
-- overlap (L,R)=[v,s,v] critical-pair lemma / (R,L)=[s,v,s] both reducts [s,s,s] / matched absurd; cons-cons disjoint
-- = the commute helper) → absorptionHasLocalConfluence (decompose both reducts, Nat.le_total dispatches 8 leaves) →
-- absorptionHasConfluence (newman + the termination) = the FIRST fully-CONFLUENT two-rule presentation with
-- genuine inter-rule critical pairs. Zero-axiom: disjoint leaves bridge cons-form↔append-form via ←doubleConsAppend +
-- ←listAppendAssoc (no simp). The decidable word problem (two-rule WordReducer) is the slice below.
#assert_no_axioms FX1Poly.OmegacE.absorptionJoinableWhenLeftShorter
#assert_no_axioms FX1Poly.OmegacE.absorptionHasLocalConfluence
#assert_no_axioms FX1Poly.OmegacE.absorptionHasConfluence

-- ABSORPTION REDUCER + DECIDABLE WORD PROBLEM (AbsorptionReducer.lean): the absorption capstone.
-- A two-rule WordReducer with a SINGLE disjunction-if scanner (both rules splice a mixed pair to [s,s], so
-- (first=v ∧ second=s) ∨ (first=s ∧ second=v) covers both). firesLeft/firesRight (Or.inl/Or.inr, NO distinctness —
-- both branches → [s,s]); monotonicity (reuse option_isSome_map); sound (fire case rcases the disjunction CONDITION
-- → rule-Left/Right); complete (absorptionRewrite_implies_reduceCells_isSome: fire case rcases the rule DISJUNCTION).
-- absorptionWordReducer bundles them (NO distinctness); decidableConvertibleModulo_absorptionSystem =
-- decidableConvertibleModulo_ofConvergent fed absorptionHasLocalConfluence + absorptionSystem_isTerminating (needs
-- v≠s) + the reducer = the FIRST FULLY-DECIDED two-rule presentation with genuine inter-rule critical pairs.
-- Faithful mirror of the gated TranspositionReducer with the two-rule disjunction-if; all zero-axiom.
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

-- SORTING / SYMMETRIC SYSTEM — GUARDED RULE FAMILY (SortingSystem.lean).
-- Parameterized by a priority slotValue : OmegacECell → Nat; the rule [a,b]→[b,a] fires for EVERY descending pair
-- (slotValue b < slotValue a) — bubble sort = the symmetric-group word problem. Membership is an EXISTENTIAL with a
-- strict-order GUARD (∃ a b, slotValue b < slotValue a ∧ rule = sortingSwapRule a b) — the genuinely-new structure
-- vs the absorption system's two-element disjunction. fires = guarded fire (⟨a,b,descending,rfl⟩); isLengthPreserving
-- = obtain the existential + rfl; the 3 length invariants instantiate the preservation lemmas. Zero-axiom.
-- The slices below add: INVERSION-count termination (all out-of-order pairs, generalizing the transposition
-- aBeforeBInversions); LOCAL CONFLUENCE with the braid critical pair [a,b,c] (slotValue a>b>c; reducts join to
-- sorted [c,b,a] via multi-step); a guarded WordReducer + decidability.
#assert_no_axioms FX1Poly.OmegacE.sortingSwapRule
#assert_no_axioms FX1Poly.OmegacE.sortingSystem
#assert_no_axioms FX1Poly.OmegacE.sortingSwapRule_fires
#assert_no_axioms FX1Poly.OmegacE.sortingSystem_isLengthPreserving
#assert_no_axioms FX1Poly.OmegacE.sortingSystem_rewritesOneStep_length_preserved
#assert_no_axioms FX1Poly.OmegacE.sortingSystem_rewritesMany_length_preserved
#assert_no_axioms FX1Poly.OmegacE.sortingSystem_convertibleModulo_length_preserved

-- SORTING INVERSION MEASURE (SortingTermination.lean): the bubble-sort termination measure.
-- countBelowThreshold (count cells with slotValue < threshold) + countInversions (total out-of-order pairs) +
-- crossInversionCount (the SUM-fold cross term across an append). The two append homomorphisms are the reusable core;
-- countInversions_append's cons case is a five-term Nat AC rearrangement (a+b)+((c+d)+e)=((a+c)+d)+(b+e), discharged by
-- explicit Nat.add_assoc/add_left_comm normalizing both sides to a+(b+(c+(d+e))) — NOT ac_rfl (leaks propext+Quot.sound),
-- the heavier analogue of the transposition aBeforeBInversions (whose cross term is a single product). Zero-axiom.
#assert_no_axioms FX1Poly.OmegacE.countBelowThreshold
#assert_no_axioms FX1Poly.OmegacE.countInversions
#assert_no_axioms FX1Poly.OmegacE.crossInversionCount
#assert_no_axioms FX1Poly.OmegacE.countBelowThreshold_append
#assert_no_axioms FX1Poly.OmegacE.countInversions_append

-- SORTING TERMINATION (SortingTermination.lean): the bubble-sort termination proper.
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

-- SORTING CONFLUENCE (SortingConfluence.lean): structural inversion + the BRAID critical pair.
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

-- SORTING LOCAL + GLOBAL CONFLUENCE (SortingConfluence.lean): the confluence headline. The prefix-split
-- trichotomy joinableWhenLeftShorter dispatches: nil = equal reducts (NOT a mismatch — both redexes coincide);
-- single = THE braid critical pair (reuses sortingBraidCriticalPairJoin, the new content vs transposition's vacuous
-- one-cell case); cons-cons = disjoint commute (mirrors transposition/absorption). hasLocalConfluence decomposes both
-- reducts + Nat.le_total dispatch; hasConfluence = newman localConfluence + sortingSystem_isTerminating (the guarded
-- family needs no external a≠b). The braid word-eqs close by listAppendAssoc reassociation + a default-transparency
-- rfl (the inner concrete-prefix appends are defeq). The sorting/symmetric presentation is CONVERGENT. Zero-axiom.
#assert_no_axioms FX1Poly.OmegacE.sortingJoinableWhenLeftShorter
#assert_no_axioms FX1Poly.OmegacE.sortingHasLocalConfluence
#assert_no_axioms FX1Poly.OmegacE.sortingHasConfluence

-- SORTING REDUCER + DECIDABILITY (SortingReducer.lean): the sorting capstone. The bounded-search reducer mirrors the
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

-- ωcE FINITE-TYPE FAMILY (OmegacEFiniteType.lean). The walking-coherent-equivalence generator family
-- is BINARY finite-type: generatorsAt enumerates exactly 2 generators per dimension (Nat match 0|1|2|baseDim+3),
-- generatorsAt_length proves the binary cardinality, mem_generatorsAt proves EXHAUSTIVENESS (every cell is listed)
-- via OmegacECell.casesOn with the membership motive + Fin-2 structure split (no Fin.cases). Standalone finite-type
-- witness; does NOT bump fxOmegacEConstructionLevel (the boundaryPresented/hlorPushout rungs of the HLOR boundary
-- presentation need the higher-cell pasting data). Zero-axiom.
#assert_no_axioms FX1Poly.OmegacE.generatorsAt
#assert_no_axioms FX1Poly.OmegacE.generatorsAt_length
#assert_no_axioms FX1Poly.OmegacE.mem_generatorsAt
-- Finite-type completion: distinctness (the 2 are DISTINCT, a 2-element Fintype per dim — decide on concrete dims,
-- higherCoherence.inj + congrArg Fin.val + Nat.noConfusion on the higher pair) + suspension-preserves-slot (the
-- "+Suspend" half: slotOf_atSlot_general extends the canonical slot round-trips over Fin 2; slotOf_suspend then
-- shows Σ keeps a generator's slot, so the binary structure is stable under suspension). Zero-axiom.
#assert_no_axioms FX1Poly.OmegacE.generatorsAt_nodup
#assert_no_axioms FX1Poly.OmegacE.slotOf_atSlot_general
#assert_no_axioms FX1Poly.OmegacE.slotOf_suspend
