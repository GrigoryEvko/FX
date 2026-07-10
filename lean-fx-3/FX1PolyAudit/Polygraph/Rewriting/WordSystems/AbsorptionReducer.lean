import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.OmegacE.AbsorptionReducer

/-! # FX1PolyAudit.Polygraph.OmegacE.AbsorptionReducer

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.OmegacE.AbsorptionReducer`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

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

end FX1PolyAudit
