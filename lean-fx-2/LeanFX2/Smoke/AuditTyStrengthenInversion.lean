import LeanFX2.Foundation.TyStrengthenInversion

/-! # Smoke/AuditTyStrengthenInversion

Reviewer-facing `#print axioms` gate for the 18 zero-axiom
`Ty.partialStrengthen?_<ctor>_isSome` inversion lemmas in
`Foundation/TyStrengthenInversion.lean`.

Each lemma decomposes a composite
`((Ty.<ctor> args).partialStrengthen? back).isSome = true`
into per-sub-field `.isSome = true` facts, used by the eventual
universal typed-strengthening driver (Block B
`Step.par.preserves_rename_image`, #2022) to discharge the
type-side hypotheses of the 78 per-arm wrappers in
`Term/StrengtheningImage/TargetImageTotality.lean`.

Each `#print axioms` line below must report
"does not depend on any axioms" — strict Layer K gate. -/

namespace LeanFX2.Smoke.AuditTyStrengthenInversion

#print axioms LeanFX2.Ty.partialStrengthen?_arrow_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_piTy_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_sigmaTy_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_listType_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_optionType_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_eitherType_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_refine_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_codata_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_equiv_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_modal_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_record_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_session_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_effect_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_glue_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_id_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_path_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_oeq_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_idStrict_isSome

end LeanFX2.Smoke.AuditTyStrengthenInversion
