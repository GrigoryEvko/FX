import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.WordSystems.OmegacEFiniteType

/-! # FX1PolyAudit.Polygraph.OmegacE.OmegacEFiniteType

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.OmegacE.OmegacEFiniteType`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

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

end FX1PolyAudit
