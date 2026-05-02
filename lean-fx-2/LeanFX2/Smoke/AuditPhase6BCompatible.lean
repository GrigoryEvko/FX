import LeanFX2.Reduction.RawParCompatible

/-! Phase 6.B substitution-compatibility chain zero-axiom audit.

5 lemmas drive the β-arms of `cd_lemma`:
* `subst0_subst_commute` — combinator equation reshaping the β reduct
* `RawTermSubst.par_lift` — lifted subst preserves pointwise par
* `subst_par_pointwise` — same term, parallel substs → parallel
* `RawStep.par.subst_par` — joint: parallel terms + parallel substs
* `RawStep.par.subst0_par` — singleton corollary (β workhorse)
-/

#print axioms LeanFX2.RawTerm.subst0_subst_commute
#print axioms LeanFX2.RawTermSubst.par_lift
#print axioms LeanFX2.RawTerm.subst_par_pointwise
#print axioms LeanFX2.RawStep.par.subst_par
#print axioms LeanFX2.RawStep.par.subst0_par
