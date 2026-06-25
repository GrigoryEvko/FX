import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.OmegacE.AbsorptionConfluence

/-! # FX1PolyAudit.Tier0.OmegacE.AbsorptionConfluence

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.OmegacE.AbsorptionConfluence`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

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

end FX1PolyAudit
