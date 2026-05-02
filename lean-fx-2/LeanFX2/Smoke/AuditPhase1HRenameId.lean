import LeanFX2.Foundation.RenameIdentity

/-! Phase 1.H zero-axiom audit — identity-renaming preservation.

These three structural lemmas are the foundation for all "identity"
proofs at higher levels (Term.rename_id_HEq, etc.).  Each must be
zero-axiom because pointwise equality + structural recursion are
both axiom-free in Lean 4. -/

#print axioms LeanFX2.RawRenaming.identity_lift_pointwise
#print axioms LeanFX2.RawTerm.rename_identity
#print axioms LeanFX2.Ty.rename_identity
