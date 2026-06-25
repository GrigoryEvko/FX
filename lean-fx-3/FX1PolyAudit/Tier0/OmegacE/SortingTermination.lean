import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.OmegacE.SortingTermination

/-! # FX1PolyAudit.Tier0.OmegacE.SortingTermination

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.OmegacE.SortingTermination`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

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

end FX1PolyAudit
