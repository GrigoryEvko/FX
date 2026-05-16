import LeanFX2.Term.WeakenInverse
import LeanFX2.Term.ContextStrengthening
import LeanFX2.Term.PartialStrengthen

/-! # AuditTermWeakenInverse — typed strengthening foundation primitives.

Smoke audit for the Phase 1 typed-strengthening foundation shipped
in `LeanFX2.Term.WeakenInverse`.

## Coverage

* **Layer 1 — Raw inversion helpers** (3 shipped):
  - `RawTerm.weakenInverse_var` — invert `RawTerm.var pos = rawOrig.weaken`
  - `RawTerm.weakenInverse_lam` — invert `RawTerm.lam body = rawOrig.weaken`
  - `RawTerm.weakenInverse_app` — invert `RawTerm.app f a = rawOrig.weaken`

* **Layer 2 — Typed weaken inversion at raw shape** (1 shipped):
  - `Term.weakenInverse_atVar` — typed inversion at `RawTerm.var` shape

* **Layer 3 — Cascade construction helpers** (3 shipped):
  - `Term.eta_shape_construct` — the canonical D2.5.5 eta-redex builder
  - `Term.weaken_var_unfolds` — `Term.weaken` of `Term.var` unfolds rfl
  - `Term.weaken_app_toRaw` — `Term.weaken` of `Term.app` distributes rfl

## Cascade unblocks

* **D2.5.5 transpPi β cascade** — load-bearing for the eta cascade
  (`lift_lam` Or.inr / typed `Step.par.arrowEta` / typed `Step.par.piEta`).
* **K12.20.U2 Reducible.cr3 typed** — same strengthening pattern.
* **CONVTRANS-B.* families** — `Step.par.invertRawAt` building block.
* **Future D2.5.6 transpSigma cascade** — pair-eta uses the same template.
* **Future K18.7 LeanKernel η reduction** — same pattern at FX1 layer.

Every shipped declaration must report "does not depend on any axioms".
The `LeanFX2Audit` target enforces this via `#assert_no_axioms` in
`Tools/AuditAll/AuditTerm.lean`. -/

namespace LeanFX2.SmokeTermWeakenInverse

-- Layer 1: raw inversion helpers
#print axioms LeanFX2.RawTerm.weakenInverse_var
#print axioms LeanFX2.RawTerm.weakenInverse_lam
#print axioms LeanFX2.RawTerm.weakenInverse_app

-- Layer 2: typed inversion at fixed raw shape
#print axioms LeanFX2.Term.weakenInverse_atUnit
#print axioms LeanFX2.Term.weakenInverse_atBoolTrue
#print axioms LeanFX2.Term.weakenInverse_atBoolFalse
#print axioms LeanFX2.Term.weakenInverse_atNatZero
#print axioms LeanFX2.Term.weakenInverse_atVar

-- Layer 3: cascade construction helpers
#print axioms LeanFX2.Term.eta_shape_construct
#print axioms LeanFX2.Term.weaken_var_unfolds
#print axioms LeanFX2.Term.weaken_app_toRaw

-- Semantic / partial strengthening certificates
#print axioms LeanFX2.RawTerm.partialStrengthen?
#print axioms LeanFX2.RawTerm.partialStrengthen?_imp_rename
#print axioms LeanFX2.RawTerm.partialStrengthen?_rename_some
#print axioms LeanFX2.PartialRawRenaming.lift_weaken_map
#print axioms LeanFX2.RawTerm.partialStrengthen?_weaken_lift
#print axioms LeanFX2.RawTerm.strengthen?
#print axioms LeanFX2.RawTerm.usesNewestSlot?
#print axioms LeanFX2.RawTerm.not_usesNewestSlot?_imp_weaken
#print axioms LeanFX2.RawTerm.weaken_not_usesNewestSlot?
#print axioms LeanFX2.Ty.partialStrengthen?
#print axioms LeanFX2.Ty.strengthen?
#print axioms LeanFX2.Ty.usesNewestSlot?
#print axioms LeanFX2.Ty.partialStrengthen?_rename_some
#print axioms LeanFX2.Ty.partialStrengthen?_rename_compat
#print axioms LeanFX2.Ty.partialStrengthen?_weaken_lift
#print axioms LeanFX2.Ty.partialStrengthen?_imp_rename
#print axioms LeanFX2.Ty.partialStrengthen?_subst0_of_success
#print axioms LeanFX2.Ty.strengthen?_weaken
#print axioms LeanFX2.Ty.strengthen?_imp_weaken
#print axioms LeanFX2.Ty.not_usesNewestSlot?_imp_weaken
#print axioms LeanFX2.ContextStrengthening.toTermRenaming
#print axioms LeanFX2.ContextStrengthening.dropNewest
#print axioms LeanFX2.ContextStrengthening.dropNewest_toTermRenaming
#print axioms LeanFX2.ContextStrengthening.lift
#print axioms LeanFX2.Term.StrengtheningResult
#print axioms LeanFX2.Term.StrengtheningResult.renamedTarget
#print axioms LeanFX2.Term.partialStrengthenTypedVarOfSurvives
#print axioms LeanFX2.Term.partialStrengthenTypedUnit
#print axioms LeanFX2.Term.partialStrengthenTypedBoolTrue
#print axioms LeanFX2.Term.partialStrengthenTypedBoolFalse
#print axioms LeanFX2.Term.partialStrengthenTypedNatZero
#print axioms LeanFX2.Term.partialStrengthenTypedInterval0
#print axioms LeanFX2.Term.partialStrengthenTypedInterval1
#print axioms LeanFX2.Term.partialStrengthenTypedListNilOfType
#print axioms LeanFX2.Term.partialStrengthenTypedOptionNoneOfType
#print axioms LeanFX2.Term.partialStrengthenTypedNatSucc
#print axioms LeanFX2.Term.partialStrengthenTypedOptionSome
#print axioms LeanFX2.Term.partialStrengthenTypedModIntro
#print axioms LeanFX2.Term.partialStrengthenTypedModElim
#print axioms LeanFX2.Term.partialStrengthenTypedSubsume
#print axioms LeanFX2.Term.partialStrengthenTypedIntervalOpp
#print axioms LeanFX2.Term.partialStrengthenTypedIntervalMeet
#print axioms LeanFX2.Term.partialStrengthenTypedIntervalJoin
#print axioms LeanFX2.Term.partialStrengthenTypedApp
#print axioms LeanFX2.Term.partialStrengthenTypedAppPi
#print axioms LeanFX2.Term.partialStrengthenTypedListCons
#print axioms LeanFX2.Term.partialStrengthenTypedEitherInlOfRightType
#print axioms LeanFX2.Term.partialStrengthenTypedEitherInrOfLeftType
#print axioms LeanFX2.Term.partialStrengthenTypedPair
#print axioms LeanFX2.Term.partialStrengthenTypedFst
#print axioms LeanFX2.Term.partialStrengthenTypedSnd
#print axioms LeanFX2.Term.partialStrengthenTypedRecordIntro
#print axioms LeanFX2.Term.partialStrengthenTypedRecordProj
#print axioms LeanFX2.Term.partialStrengthen?
#print axioms LeanFX2.Term.partialStrengthen?_imp_indices_rename
#print axioms LeanFX2.Term.strengthen?
#print axioms LeanFX2.Term.usesNewestSlot?
#print axioms LeanFX2.Term.strengthen?_imp_indices_weaken
#print axioms LeanFX2.Term.not_usesNewestSlot?_imp_indices_weaken

end LeanFX2.SmokeTermWeakenInverse
