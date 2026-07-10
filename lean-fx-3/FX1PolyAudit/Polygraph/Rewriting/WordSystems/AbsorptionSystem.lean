import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.WordSystems.AbsorptionSystem

/-! # FX1PolyAudit.Polygraph.OmegacE.AbsorptionSystem

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.OmegacE.AbsorptionSystem`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

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

end FX1PolyAudit
