import LeanFX2.Term.StrengtheningImage

/-! # AuditTypedInversion — typed `Term.app_inv` family axiom audit.

Smoke audit for the typed structural inversion lemmas shipped in
`LeanFX2.Term.TypedInversion`.

## Coverage

Three inversion lemmas for `RawTerm.app` shape:

* `Term.app_inv` — universal form (output type `targetType` free,
  disjunction over `Term.app` / `Term.appPi` arms).
* `Term.app_inv_arrow` — arrow-output specialization.
* `Term.app_inv_pi`   — Π-output specialization.

## Cascade unblocks

These lemmas are the typed-η-redesign prerequisite per
`feedback_typed_eta_lam_inv_cascade_blocker_2026_05_16.md`.  Once
shipped, downstream consumers can recover typed `fnTerm` + `argTerm`
from a typed `Term.app`-shape body — load-bearing for `lift_lam`'s
η-arm, subject reduction app cases, and decidable conversion's
function-application reasoning.

Every shipped declaration must report "does not depend on any axioms".
The `LeanFX2Audit` target enforces this via `#assert_no_axioms` in
`Tools/AuditAll/AuditTerm.lean`. -/

namespace LeanFX2.SmokeTypedInversion

-- Universal and specialized inversions for `RawTerm.app` shape
#print axioms LeanFX2.Term.app_inv
#print axioms LeanFX2.Term.app_inv_arrow
#print axioms LeanFX2.Term.app_inv_pi

-- Typed weaken inversion at arrow type (Option form).  Thin wrapper
-- around `Term.unweaken?` specialized to `Ty.arrow A B` indices.
-- The universal existence form is gated on extending
-- `StrengtheningResult` with a `termRenames` field.
#print axioms LeanFX2.Term.weaken_inv_arrow_option

-- Supporting infrastructure shipped alongside the typed weaken
-- inversion cascade prerequisites.
#print axioms LeanFX2.Ty.weaken_inj
#print axioms LeanFX2.Term.weakenInverse_atVarZero

-- Typed strengthening image soundness scaffold.
#print axioms LeanFX2.Term.StrengtheningSoundness
#print axioms LeanFX2.Term.heq_cast_right
#print axioms LeanFX2.Term.rename_var_heq
#print axioms LeanFX2.Term.partialStrengthenTypedVarOfSurvives_sound
#print axioms LeanFX2.Term.partialStrengthenTypedUnit_sound
#print axioms LeanFX2.Term.partialStrengthenTypedBoolTrue_sound
#print axioms LeanFX2.Term.partialStrengthenTypedBoolFalse_sound
#print axioms LeanFX2.Term.partialStrengthenTypedNatZero_sound
#print axioms LeanFX2.Term.partialStrengthenTypedInterval0_sound
#print axioms LeanFX2.Term.partialStrengthenTypedInterval1_sound
#print axioms LeanFX2.Term.partialStrengthenTypedListNilOfType_sound
#print axioms LeanFX2.Term.partialStrengthenTypedOptionNoneOfType_sound
#print axioms LeanFX2.Term.partialStrengthenTypedNatSucc_sound
#print axioms LeanFX2.Term.partialStrengthenTypedOptionSome_sound
#print axioms LeanFX2.Term.partialStrengthenTypedModIntro_sound
#print axioms LeanFX2.Term.partialStrengthenTypedModElim_sound
#print axioms LeanFX2.Term.partialStrengthenTypedSubsume_sound
#print axioms LeanFX2.Term.partialStrengthenTypedListCons_sound
#print axioms LeanFX2.Term.partialStrengthenTypedIntervalOpp_sound
#print axioms LeanFX2.Term.partialStrengthenTypedIntervalMeet_sound
#print axioms LeanFX2.Term.partialStrengthenTypedIntervalJoin_sound

end LeanFX2.SmokeTypedInversion
