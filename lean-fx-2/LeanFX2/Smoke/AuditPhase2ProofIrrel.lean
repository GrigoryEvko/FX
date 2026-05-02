import LeanFX2.Term.ProofIrrel

/-! Phase 2 zero-axiom audit — Term proof-irrelevance lemmas.

These two lemmas exploit Lean 4's Prop proof irrelevance:
- TermRenaming is `Prop` (consistency predicate), so two proofs of the
  same TermRenaming are literally equal — Term.rename only depends
  on the underlying RawRenaming
- TermSubst is `Type` (function from positions to Term values), so
  pointwise agreement gives Term.subst equality via subst_pointwise -/

#print axioms LeanFX2.Term.rename_proof_irrel
#print axioms LeanFX2.Term.subst_proof_irrel
