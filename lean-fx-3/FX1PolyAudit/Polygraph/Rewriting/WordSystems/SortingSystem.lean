import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.OmegacE.SortingSystem

/-! # FX1PolyAudit.Polygraph.OmegacE.SortingSystem

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.OmegacE.SortingSystem`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

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

end FX1PolyAudit
