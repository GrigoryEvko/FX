import LeanFX2.Foundation.TyStrengthenInversion

/-! # Smoke/AuditTyStrengthenInversion

Reviewer-facing `#print axioms` gate for the 24 zero-axiom
`Ty.partialStrengthen?_<ctor>_isSome` inversion lemmas in
`Foundation/TyStrengthenInversion.lean`.

Each lemma decomposes a composite
`((Ty.<ctor> args).partialStrengthen? back).isSome = true`
into per-sub-field `.isSome = true` facts, used by the eventual
universal typed-strengthening driver (Block B
`Step.par.preserves_rename_image`, #2022) to discharge the
type-side hypotheses of the 78 per-arm wrappers in
`Term/StrengtheningImage/TargetImageTotality.lean`.

Coverage: 18 multi-field composite ctors (arrow / piTy / sigmaTy /
listType / optionType / eitherType / refine / codata / equiv /
modal / record / session / effect / glue / id / path / oeq /
idStrict) plus 6 closed-atomic unconditional ctors (bool / empty /
interval / nat / unit / universe).

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

-- Closed-atomic unconditional ctors (rfl-proved one-liners).
#print axioms LeanFX2.Ty.partialStrengthen?_bool_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_empty_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_interval_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_nat_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_unit_isSome
#print axioms LeanFX2.Ty.partialStrengthen?_universe_isSome

end LeanFX2.Smoke.AuditTyStrengthenInversion
