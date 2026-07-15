import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Term.Core.RawTermFoldNonVarCommute

/-! # FX1PolyAudit.Axis.Term.Core.RawTermFoldNonVarCommute

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.Term.Core.RawTermFoldNonVarCommute`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Generic non-variable cell commutation for fold traversals: the substrate for subst/rename through an
-- abstract formation cell.  fold_mkGen_of_ne_var exposes the fold non-variable branch for an abstract
-- non-gen_var generator (dsimp [fold] + dif_neg); subst/rename_mkGen_of_ne_var are the traversal corollaries
-- (canonical_algebra_eq_mkGen rebuild).  The payload cast is
-- Generator.payload_scope_invariant_of_not_var (the generator enumeration in one place).  The category-C
-- formation-family consumers (HasTypeDescSubstitution/Weakening + grown twins) discharge their pi/sigma
-- cases through it generically, so a new formation row touches none of them.
#assert_no_axioms FX1Poly.Core.fold_mkGen_of_ne_var

#assert_no_axioms FX1Poly.Core.RawTerm.subst_mkGen_of_ne_var

#assert_no_axioms FX1Poly.Core.RawTerm.rename_mkGen_of_ne_var

end FX1PolyAudit
