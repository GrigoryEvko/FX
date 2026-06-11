import FX1Poly.Extension.ProfileExtension
import FX1Poly.Core.ProfileAdmission
/-! # FX1Poly/Extension/AdmissibleProfileTensor
    — the extendProfile admission transfer (the QUARANTINED extension PoC's ledger fragment)

QUARANTINE NOTE: this Extension subsystem is a PROOF OF CONCEPT,
verified to cohere and deliberately FROZEN.  The kernel-native content
that used to live here — the capability lattice ORDER theory, the
`AdmissibleProfile` admission discipline, the cellular tensor
obligation shapes with their diagonal inhabitant, and the (T7)
Zwart-Marsden register + gate — is INTEGRATED INTO THE KERNEL:
`FX1Poly/Tier0/AxisObligation.lean` (the lattice order) and
`FX1Poly/Core/ProfileAdmission.lean` (admissions, tensor shapes,
register).  What remains here is exactly the PoC-specific fragment:
theorems ABOUT `extendProfile` and `ProfileExtension`.

1. `extendProfile_preserves_admissible` — the ledger admission
   transfer: extending a ledger-admissible profile yields a
   ledger-admissible profile at the meet capability record.
   Bookkeeping transfer, not actual metatheory.  The full admission
   theorem (canonicity / normalization / SN about the extended kernel
   itself) is recorded by `FullAdmissionObligations`, which is
   deliberately not inhabited.

2. The honesty pins: the `fxExtensionConstructionLevel` ledger stays
   below `admissibleProfileTheorem`.

Anti-fake-completion discipline: no axiom, no sorry, no placeholder
inhabitant.  Unproved targets are types without terms.

Reference: polycell.md §3.0.7 (T1)-(T8), §3.14.
-/

namespace FX1Poly.Extension

open Core Tier0

/-! ## The headline (#216) — proved for the ledger reading

`extendProfile` preserves every construction ledger definitionally
(the ten `extendProfile_preserves_*` theorems), and the extended
capability record is the meet of base and extension records.  A meet
claim is below the base claim, so base backing transfers verbatim. -/

/-- ★ The ledger admission theorem: extending a ledger-admissible
profile yields a ledger-admissible profile whose capability record is
`extendedCapabilities` (base meet extension).

This is the PROVABLE fragment of the polycell.md §3.14 admission
aspiration.  What it does NOT say: that any canonicity/normalization/
SN THEOREM about the extended kernel exists.  It says the extended
bookkeeping never advertises a capability the extended profile's own
construction ledgers cannot back — because `extendProfile` preserves
the ledgers and the meet only ever lowers claims. -/
def extendProfile_preserves_admissible
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile)
    (baseAdmissible : AdmissibleProfile baseProfile) :
    AdmissibleProfile (extendProfile baseProfile extension) where
  capabilities :=
    extendedCapabilities baseProfile extension baseAdmissible.capabilities
  canonicityBacked := fun claimed =>
    baseAdmissible.canonicityBacked
      (CapabilityStatus.eq_available_of_isBelow_of_available
        (MetatheoreticCapabilities.meet_isBelow_left
          baseAdmissible.capabilities extension.capabilities).1
        claimed)
  normalizationBacked := fun claimed =>
    baseAdmissible.normalizationBacked
      (CapabilityStatus.eq_available_of_isBelow_of_available
        (MetatheoreticCapabilities.meet_isBelow_left
          baseAdmissible.capabilities extension.capabilities).2.1
        claimed)
  decidableConversionBacked := fun claimed =>
    baseAdmissible.decidableConversionBacked
      (CapabilityStatus.eq_available_of_isBelow_of_available
        (MetatheoreticCapabilities.meet_isBelow_left
          baseAdmissible.capabilities
          extension.capabilities).2.2.2.2.2.2.1
        claimed)

/-- The extended admission carries exactly the meet capability record. -/
theorem extendProfile_preserves_admissible_capabilities
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile)
    (baseAdmissible : AdmissibleProfile baseProfile) :
    (extendProfile_preserves_admissible baseProfile extension
        baseAdmissible).capabilities =
      baseAdmissible.capabilities.meet extension.capabilities := rfl

/-- The eta demonstration extension applied to the FX bottom admission
stays at bottom — the demonstration inherits no capability. -/
theorem fxWithEta_admission_capabilities_eq_bot :
    (extendProfile_preserves_admissible fxProfile etaReductionExtension
        fxProfileLedgerAdmission).capabilities =
      MetatheoreticCapabilities.bot :=
  MetatheoreticCapabilities.meet_bot_right MetatheoreticCapabilities.bot

/-! ## The full admission obligations — stated, NOT inhabited

The polycell.md §3.14 aspiration is not the ledger transfer above but
genuine metatheory transfer.  The record below pins that obligation
shape.  No value of it is constructed anywhere in the tree; building
one is the `metatheoryTransfer` / `admissibleProfileTheorem` rung of
`ExtensionConstructionLevel`, and the `fxExtension_hasNo*` theorems
in ProfileExtension.lean prove the rung is NOT reached. -/

structure FullAdmissionObligations (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile) where
  /-- The ledger fragment (shipped above). -/
  ledgerAdmission :
    AdmissibleProfile baseProfile →
      AdmissibleProfile (extendProfile baseProfile extension)
  /-- The genuine obligation: the extension's interface generators and
  reduction rules are realized on the kernel syntax, and every
  capability the extension record claims `available` is re-proved for
  the EXTENDED kernel (canonicity, normalization, SN, decidability —
  per claimed field).  The current scaffold has no kernel-level
  realization of `PolynomialInterface`, so this field is stated
  against the only thing the substrate can express today: the
  per-axis construction levels must ADVANCE (not merely persist) for
  each claimed capability.  Once the algebra-extension rung lands,
  this field is to be restated against the realized generators. -/
  metatheoryRealized :
    extension.capabilities.canonicityStatus = .available →
      (extendProfile baseProfile
          extension).stcConstructionLevel.hasCanonicityTheorem = true
  /-- Interaction-law obligation: bilax compatibility against EVERY
  axis of the base profile, not only the generator-count bookkeeping
  the current `BilaxCompatibilityEvidence` records. -/
  interactionLawsTotal :
    extension.interface.generatorCount = 0 ∨
      extension.fireTriangleRestriction.isSome = true

/-- POST-SN-100 STATUS CHANGE.  Before the canonicity ledger flip this
spot held `fullAdmission_metatheoryRealized_unrealizable_for_fx`: an
`available` canonicity claim made `metatheoryRealized` underivable,
because `extendProfile` preserves the base STC ledger and `fxProfile`
had `hasCanonicityTheorem = false`.  That theorem is now FALSE —
`fxProfile`'s ledger carries the bool canonicity theorem
(`canonicityViaSTC`), so the obligation's formal statement holds by
ledger PERSISTENCE, as this replacement pins.

HONESTY BOUNDARY: persistence-discharge does NOT realize the field
docstring's "must ADVANCE (not merely persist)" intent — since
`extendProfile` preserves every construction level, genuine
advancement remains structurally impossible, and the field's formal
statement no longer distinguishes the two.  The restatement decision
is TAKEN in `AdmissionAdvanceBoundary.lean`: the persist-form field
stays as-is, the advance form is stated separately
(`AdvancingAdmissionObligations`) and proved UNIVERSALLY unrealizable
under the level-preserving `extendProfile`
(`advancingAdmission_canonicity_unrealizable`) — the flip-proof
restoration of the structural point the deleted theorem made. -/
theorem fullAdmission_metatheoryRealized_canonicityRung_dischargeable
    (extension : ProfileExtension fxProfile) :
    (extendProfile fxProfile
        extension).stcConstructionLevel.hasCanonicityTheorem = true := by
  rw [extendProfile_preserves_stcConstructionLevel]
  exact fxProfile_stcHasCanonicityTheorem

/-! ## Honesty pins

The construction-level ledger stays below the admission-theorem rung:
the ledger fragment above is `extendProfile` bookkeeping plus the
kernel's lattice laws, not the §3.14 metatheory-transfer theorem.
The cellular tensor obligation shapes and their diagonal inhabitant
live in the KERNEL (`FX1Poly/Core/ProfileAdmission.lean`); no
heterogeneous tensor and no realized GAT-tensor algorithm exists. -/

theorem extensionLedger_stillBelow_metatheoryTransfer :
    fxExtensionConstructionLevel.hasMetatheoryTransfer = false := rfl

theorem extensionLedger_stillBelow_admissibleProfileTheorem :
    fxExtensionConstructionLevel.hasAdmissibleProfileTheorem = false := rfl

end FX1Poly.Extension
