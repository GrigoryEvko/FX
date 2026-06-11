import FX1Poly.Extension.AdmissibleProfileTensor
import FX1Poly.Extension.ProfileLens
/-! # FX1Poly/Extension/AdmissionAdvanceBoundary
    — the persist-vs-advance DECISION + the admissibleProfileTheorem rung verdict

Two deferred questions are answered here as committed theorems.

## 1. The persist-vs-advance restatement (deferred by the SN-100 collateral)

`FullAdmissionObligations.metatheoryRealized` was written to demand
that a claimed capability be RE-PROVED for the extended kernel — "the
per-axis construction levels must ADVANCE (not merely persist)".  Its
formal statement (`hasCanonicityTheorem = true` on the extended
profile) captured that intent only while the base ledger was false;
the SN-100/SN-101 flips made it dischargeable by PERSISTENCE.  The
DECISION: keep the persist-form field as-is (its dischargeability is
pinned by `fullAdmission_metatheoryRealized_canonicityRung_dischargeable`)
and state the ADVANCE form separately — `AdvancingAdmissionObligations`
below — then prove it UNIVERSALLY UNREALIZABLE
(`advancingAdmission_canonicity_unrealizable`): `extendProfile`
preserves every construction level definitionally, so "the extended
ledger backs what the base did not" is contradictory for EVERY base
profile, not only `fxProfile`.  This restores, in a flip-proof form,
the structural point the pre-SN-100 unrealizability theorem made: the
current extension bookkeeping cannot manufacture metatheory.  (A
realizable advance-form requires extension application that genuinely
GROWS the kernel — the algebra-extension rung.)

## 2. Why the `admissibleProfileTheorem` rung stays false (SN-108 verdict)

NOT a ledger flip.  The `ExtensionConstructionLevel` ladder is
CUMULATIVE: the top rung structurally entails the three unfilled rungs
(`hasAdmissibleProfileTheorem_requires_*` below — algebra extension,
interaction-law proofs, metatheory transfer), and the ledger reading
shipped as #216 (`extendProfile_preserves_admissible`) was never the
rung's content — it transfers BOOKKEEPING, not theorems.  The rung is
DOUBLY blocked today:

  * no realized generator extension exists to transfer metatheory TO —
    every constructible `ProfileExtension` has zero interface
    generators (`profileExtension_generatorCount_zero`); and
  * even granting one, advancement-by-extension is contradictory under
    the current level-preserving `extendProfile` (theorem 1 above).

The ledger therefore rests at `.profileLensInstance`
(`fxExtension_hasNoAdmissibleProfileTheorem`,
`extensionLedger_stillBelow_admissibleProfileTheorem` — both still
true, both gated).  The unlock path is the `algebraExtension` rung:
realized generators plus a level-ADVANCING extension application.

Zero-axiom; gated in `FX1PolyAudit/AuditProfile.lean`. -/

namespace FX1Poly.Extension

open FX1Poly.Core FX1Poly.Tier0

/-- The ADVANCE-form admission obligation: a claimed capability must be
backed by the EXTENDED profile's ledger AND not already backed by the
base — the extension itself must have advanced the construction level.
This is the formal statement of the "must ADVANCE (not merely
persist)" intent that `FullAdmissionObligations.metatheoryRealized`
lost when the base ledger flipped. -/
structure AdvancingAdmissionObligations (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile) where
  /-- An available canonicity claim demands a canonicity rung the BASE
  did not have. -/
  canonicityAdvances :
    extension.capabilities.canonicityStatus = .available →
      (extendProfile baseProfile
          extension).stcConstructionLevel.hasCanonicityTheorem = true ∧
        baseProfile.stcConstructionLevel.hasCanonicityTheorem = false
  /-- An available normalization claim demands a normalization rung the
  BASE did not have. -/
  normalizationAdvances :
    extension.capabilities.normalizationStatus = .available →
      (extendProfile baseProfile
          extension).stcConstructionLevel.hasNormalizationTheorem = true ∧
        baseProfile.stcConstructionLevel.hasNormalizationTheorem = false

/-- ★ **The advance-form is universally unrealizable** (canonicity
rung): for EVERY base profile and extension, an available canonicity
claim refutes `AdvancingAdmissionObligations` — `extendProfile`
preserves the STC construction level definitionally, so the extended
ledger backs exactly what the base ledger backs.  Flip-proof: unlike
the pre-SN-100 `fxProfile`-specific unrealizability theorem, no ledger
flip can falsify this statement. -/
theorem advancingAdmission_canonicity_unrealizable
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile)
    (claimed : extension.capabilities.canonicityStatus = .available)
    (obligations : AdvancingAdmissionObligations baseProfile extension) :
    False := by
  have advanced := obligations.canonicityAdvances claimed
  rw [extendProfile_preserves_stcConstructionLevel] at advanced
  exact Bool.noConfusion (advanced.1.symm.trans advanced.2)

/-- The normalization-rung twin of the universal unrealizability. -/
theorem advancingAdmission_normalization_unrealizable
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile)
    (claimed : extension.capabilities.normalizationStatus = .available)
    (obligations : AdvancingAdmissionObligations baseProfile extension) :
    False := by
  have advanced := obligations.normalizationAdvances claimed
  rw [extendProfile_preserves_stcConstructionLevel] at advanced
  exact Bool.noConfusion (advanced.1.symm.trans advanced.2)

/-! ## The cumulativity gating pins

The ladder is cumulative, so the top rung structurally entails the
three unfilled rungs — claiming `admissibleProfileTheorem` without
algebra extension, interaction-law proofs, and metatheory transfer is
not merely dishonest but impossible at the `Bool`-table level. -/

/-- The top rung entails metatheory transfer. -/
theorem hasAdmissibleProfileTheorem_requires_metatheoryTransfer :
    (level : ExtensionConstructionLevel) →
      level.hasAdmissibleProfileTheorem = true →
        level.hasMetatheoryTransfer = true
  | .interfaceLedger, claimed => Bool.noConfusion claimed
  | .localAdmissionRecord, claimed => Bool.noConfusion claimed
  | .profileTowerBookkeeping, claimed => Bool.noConfusion claimed
  | .profileLensInstance, claimed => Bool.noConfusion claimed
  | .algebraExtension, claimed => Bool.noConfusion claimed
  | .interactionLawProofs, claimed => Bool.noConfusion claimed
  | .metatheoryTransfer, claimed => Bool.noConfusion claimed
  | .admissibleProfileTheorem, _ => rfl

/-- The top rung entails interaction-law proofs. -/
theorem hasAdmissibleProfileTheorem_requires_interactionLawProofs :
    (level : ExtensionConstructionLevel) →
      level.hasAdmissibleProfileTheorem = true →
        level.hasInteractionLawProofs = true
  | .interfaceLedger, claimed => Bool.noConfusion claimed
  | .localAdmissionRecord, claimed => Bool.noConfusion claimed
  | .profileTowerBookkeeping, claimed => Bool.noConfusion claimed
  | .profileLensInstance, claimed => Bool.noConfusion claimed
  | .algebraExtension, claimed => Bool.noConfusion claimed
  | .interactionLawProofs, claimed => Bool.noConfusion claimed
  | .metatheoryTransfer, claimed => Bool.noConfusion claimed
  | .admissibleProfileTheorem, _ => rfl

/-- The top rung entails a realized algebra extension. -/
theorem hasAdmissibleProfileTheorem_requires_algebraExtension :
    (level : ExtensionConstructionLevel) →
      level.hasAdmissibleProfileTheorem = true →
        level.hasAlgebraExtension = true
  | .interfaceLedger, claimed => Bool.noConfusion claimed
  | .localAdmissionRecord, claimed => Bool.noConfusion claimed
  | .profileTowerBookkeeping, claimed => Bool.noConfusion claimed
  | .profileLensInstance, claimed => Bool.noConfusion claimed
  | .algebraExtension, claimed => Bool.noConfusion claimed
  | .interactionLawProofs, claimed => Bool.noConfusion claimed
  | .metatheoryTransfer, claimed => Bool.noConfusion claimed
  | .admissibleProfileTheorem, _ => rfl

/-- The double block, assembled: were the current ledger to claim the
top rung, it would have to claim a realized algebra extension — but no
constructible extension carries even one interface generator
(`profileExtension_generatorCount_zero`), so there is nothing for the
claimed algebra extension to consist of.  Together with the universal
advance-unrealizability above, the `admissibleProfileTheorem` rung is
out of reach until extension application genuinely grows the kernel. -/
theorem admissibleProfileTheorem_blocked_byGeneratorlessExtensions
    {baseProfile : PolyProfile}
    (extension : ProfileExtension baseProfile) :
    extension.interface.generatorCount = 0 ∧
      fxExtensionConstructionLevel.hasAdmissibleProfileTheorem = false :=
  ⟨profileExtension_generatorCount_zero extension,
    fxExtension_hasNoAdmissibleProfileTheorem⟩

end FX1Poly.Extension
