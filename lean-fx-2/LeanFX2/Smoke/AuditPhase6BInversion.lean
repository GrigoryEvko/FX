import LeanFX2.Reduction.RawParInversion
import LeanFX2.Confluence.RawParStarCong

/-! Phase 6.B inversion-lemma zero-axiom audit.

These 16 inversion lemmas use `cases` on a single-Nat-indexed Prop
inductive (RawStep.par).  Per `feedback_lean_match_arity_axioms.md`,
single-Nat-indexed inductives don't trigger propext+Quot.sound on
`cases` — but verify per-lemma anyway. -/

#print axioms LeanFX2.RawStep.par.lam_inv
#print axioms LeanFX2.RawStep.par.pair_inv
#print axioms LeanFX2.RawStep.par.refl_inv
#print axioms LeanFX2.RawStep.par.unit_inv
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

/-! ## Phase 3 (#1590 TYPED-SR-TERM-CONSTRUCTION) — multi-step canonical inversions

`RawStep.parStar.<head>_inv` lifts the single-step inversions
through chain induction.  Each is a one-line specialization of the
generic `canonical_inv_helper` private lemma.  Used by
`Conv.canonicalForm_<head>` corollaries to constrain target raw form
when source has a canonical-head raw projection. -/

#print axioms LeanFX2.RawStep.parStar.unit_inv
#print axioms LeanFX2.RawStep.parStar.boolTrue_inv
#print axioms LeanFX2.RawStep.parStar.boolFalse_inv
#print axioms LeanFX2.RawStep.parStar.natZero_inv
#print axioms LeanFX2.RawStep.parStar.listNil_inv
#print axioms LeanFX2.RawStep.parStar.optionNone_inv
#print axioms LeanFX2.RawStep.parStar.var_inv
#print axioms LeanFX2.RawStep.parStar.universeCode_inv
#print axioms LeanFX2.RawStep.parStar.natSucc_inv
