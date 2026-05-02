import LeanFX2.Term.Inversion

/-! Phase 7.A — Term type-inversion lemmas zero-axiom audit.

11 inversions for unambiguous-raw-shape Term ctors.  Given a
typed `Term ctx ty (.<ctor> ...)`, recover the type structure
(equality or existential).

These are the foundation for the future Phase 7 subject-reduction
theorem `Step.par.fromRaw` — the cong cases require extracting
typed sub-terms from a typed source whose raw matches a particular
shape, and these inversions provide the type-side of that
extraction.
-/

namespace LeanFX2.SmokePhase7ATypeInversions

#print axioms LeanFX2.Term.unit_ty_inv
#print axioms LeanFX2.Term.boolTrue_ty_inv
#print axioms LeanFX2.Term.boolFalse_ty_inv
#print axioms LeanFX2.Term.natZero_ty_inv
#print axioms LeanFX2.Term.natSucc_ty_inv
#print axioms LeanFX2.Term.listNil_ty_inv
#print axioms LeanFX2.Term.listCons_ty_inv
#print axioms LeanFX2.Term.optionNone_ty_inv
#print axioms LeanFX2.Term.optionSome_ty_inv
#print axioms LeanFX2.Term.eitherInl_ty_inv
#print axioms LeanFX2.Term.eitherInr_ty_inv
#print axioms LeanFX2.Term.refl_ty_inv
#print axioms LeanFX2.Term.pair_ty_inv

#print axioms LeanFX2.Term.unit_unique
#print axioms LeanFX2.Term.boolTrue_unique
#print axioms LeanFX2.Term.boolFalse_unique
#print axioms LeanFX2.Term.natZero_unique
#print axioms LeanFX2.Term.listNil_unique
#print axioms LeanFX2.Term.optionNone_unique

end LeanFX2.SmokePhase7ATypeInversions
