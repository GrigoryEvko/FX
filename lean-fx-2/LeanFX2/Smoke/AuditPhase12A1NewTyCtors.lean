import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Subst
import LeanFX2.Foundation.RenameIdentity
import LeanFX2.Foundation.IsClosedTy

/-! # AuditPhase12A1NewTyCtors

D1.5 audit: 13 new Ty constructors and their associated rename /
substitution operations propagate through the kernel without
introducing axioms.

Every declaration listed must report "does not depend on any axioms".
-/

#print axioms LeanFX2.Ty
#print axioms LeanFX2.Ty.rename
#print axioms LeanFX2.Ty.weaken
#print axioms LeanFX2.Ty.rename_pointwise
#print axioms LeanFX2.Ty.rename_compose
#print axioms LeanFX2.Ty.weaken_rename_commute
#print axioms LeanFX2.Ty.subst
#print axioms LeanFX2.Ty.subst0
#print axioms LeanFX2.Ty.subst_pointwise
#print axioms LeanFX2.Ty.subst_rename_commute
#print axioms LeanFX2.Ty.rename_subst_commute
#print axioms LeanFX2.Ty.subst0_rename_commute
#print axioms LeanFX2.Ty.subst_identity
#print axioms LeanFX2.Ty.weaken_subst_singleton
#print axioms LeanFX2.Ty.weaken_subst_commute
#print axioms LeanFX2.Ty.subst_compose
#print axioms LeanFX2.Ty.subst0_subst_commute
#print axioms LeanFX2.Ty.rename_identity
#print axioms LeanFX2.IsClosedTy
#print axioms LeanFX2.IsClosedTy.decide
