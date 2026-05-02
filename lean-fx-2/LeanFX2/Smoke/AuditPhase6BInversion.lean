import LeanFX2.Reduction.RawParInversion

/-! Phase 6.B inversion-lemma zero-axiom audit.

These 16 inversion lemmas use `cases` on a single-Nat-indexed Prop
inductive (RawStep.par).  Per `feedback_lean_match_arity_axioms.md`,
single-Nat-indexed inductives don't trigger propext+Quot.sound on
`cases` — but verify per-lemma anyway. -/

#print axioms LeanFX2.RawStep.par.lam_inv
#print axioms LeanFX2.RawStep.par.pair_inv
#print axioms LeanFX2.RawStep.par.refl_inv
#print axioms LeanFX2.RawStep.par.boolTrue_inv
#print axioms LeanFX2.RawStep.par.boolFalse_inv
#print axioms LeanFX2.RawStep.par.natZero_inv
#print axioms LeanFX2.RawStep.par.natSucc_inv
#print axioms LeanFX2.RawStep.par.listNil_inv
#print axioms LeanFX2.RawStep.par.listCons_inv
#print axioms LeanFX2.RawStep.par.optionNone_inv
#print axioms LeanFX2.RawStep.par.optionSome_inv
#print axioms LeanFX2.RawStep.par.eitherInl_inv
#print axioms LeanFX2.RawStep.par.eitherInr_inv
#print axioms LeanFX2.RawStep.par.modIntro_inv
#print axioms LeanFX2.RawStep.par.modElim_inv
#print axioms LeanFX2.RawStep.par.subsume_inv
