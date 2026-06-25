import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.OmegacE.SortingConfluence

/-! # FX1PolyAudit.Tier0.OmegacE.SortingConfluence

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.OmegacE.SortingConfluence`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

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

end FX1PolyAudit
