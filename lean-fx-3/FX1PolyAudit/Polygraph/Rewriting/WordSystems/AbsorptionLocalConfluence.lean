import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.WordSystems.AbsorptionLocalConfluence

/-! # FX1PolyAudit.Polygraph.OmegacE.AbsorptionLocalConfluence

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.OmegacE.AbsorptionLocalConfluence`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

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

end FX1PolyAudit
