import LeanFX2.Foundation.RawPartialRename.IsSomeInversion

/-! # Smoke/AuditRawIsSomeInversion

Reviewer-facing `#print axioms` gate for the 6 zero-axiom
`RawTerm.partialRename?_<ctor>_isSome` inversion lemmas in
`Foundation/RawPartialRename/IsSomeInversion.lean`.

Raw-side siblings of the Ty inversion lemmas; pilot covering
binder (lam), Option.mapTwo binary (app, pair, listCons), and
direct match single-child (fst, snd) shapes.

Each `#print axioms` line below must report
"does not depend on any axioms" — strict Layer K gate. -/

namespace LeanFX2.Smoke.AuditRawIsSomeInversion

#print axioms LeanFX2.RawTerm.partialRename?_lam_isSome
#print axioms LeanFX2.RawTerm.partialRename?_app_isSome
#print axioms LeanFX2.RawTerm.partialRename?_pair_isSome
#print axioms LeanFX2.RawTerm.partialRename?_fst_isSome
#print axioms LeanFX2.RawTerm.partialRename?_snd_isSome
#print axioms LeanFX2.RawTerm.partialRename?_listCons_isSome

end LeanFX2.Smoke.AuditRawIsSomeInversion
