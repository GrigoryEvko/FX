import LeanFX2.Surface.KernelEnvCorrespondence

/-! # Phase 10.B audit: env-aware ⊇ env-free correspondence

After the Phase 12.A.4 scope reduction, only `Literal.bridge_inclusion`
remains in `KernelEnvCorrespondence.lean`.  The 5-theorem mutual
block was removed pending a propext-clean encoding (deferred to v1.1+).

This audit verifies the remaining theorems are zero-axiom. -/

#print axioms LeanFX2.Surface.Env.empty_lookup_eq
#print axioms LeanFX2.Surface.Literal.bridge_inclusion
