import FX1Poly.Extension.ProfileExtension
/-!
# AdmissibleProfile + Cellular Tensor Obligation Shapes (§3.0.7, §3.14)

This file states the two headline extension-calculus targets as honest
obligation shapes over the canonical substrate:

1. The ledger-backed `AdmissibleProfile` predicate and the PROVED
   ledger fragment `extendProfile_preserves_admissible` — every
   capability the extended ledger claims is still backed by the
   extended profile's own construction ledgers.  This is the narrow
   mechanizable slice of the polycell.md §3.14 admission theorem: it
   transfers ledger-backed capability CLAIMS along `extendProfile`,
   not actual metatheory.  The full admission theorem (canonicity /
   normalization / SN about the extended kernel itself) is recorded
   by `FullAdmissionObligations`, which is deliberately not
   inhabited here.

2. The §3.0.7 FX PolyCell Cellular Tensor obligations (T1)-(T3) as
   the record shape `CellularTensorObligations`, plus the (T7)
   Zwart-Marsden no-go register.  Only the (T3) capability-meet
   LATTICE machinery ships as theorems now (meet is the greatest
   lower bound of the finite capability lattice, and the order is
   decidable).  (T1) construction and (T2) BKS-sconing preservation
   are the open research program polycell.md §3.0.7 describes; no
   `CellularTensorObligations` value is constructed here and the
   `fxExtensionConstructionLevel` ledger stays below
   `admissibleProfileTheorem`.

Anti-fake-completion discipline: no axiom, no sorry, no placeholder
inhabitant.  Unproved targets are types without terms, and the
absence is pinned by the `hasNoAdmissibleProfileTheorem` ledger
theorems at the bottom of this file.

Reference: polycell.md §3.0.7 (T1)-(T8), §3.14; Almeida vol I
(arXiv 2511, GAT syntactic tensor); Bocquet-Kaposi-Sattler
arXiv:2302.05190 (internal sconing); Zwart-Marsden arXiv:1811.06460
(distributive-law no-go theorems).
Zero external dependencies.
-/

namespace FX1Poly.Tier0

/-! ## Capability lattice order — the (T3) substrate

`MetatheoreticCapabilities` ships with a componentwise `meet`.  The
(T3) honesty-ledger statement `capabilities(tensor) <= meetOfFactors`
needs the induced partial ORDER.  Both layers (per-status and
per-record) are finite, so the order is decidable and the
greatest-lower-bound laws are case checks. -/

/-- The capability-status order: `unavailable` is below `available`.
A status is below another when claiming it concedes at least as much. -/
def CapabilityStatus.isBelow (statusA statusB : CapabilityStatus) : Prop :=
  statusA.meet statusB = statusA

instance (statusA statusB : CapabilityStatus) :
    Decidable (statusA.isBelow statusB) :=
  inferInstanceAs (Decidable (statusA.meet statusB = statusA))

theorem CapabilityStatus.isBelow_refl (status : CapabilityStatus) :
    status.isBelow status :=
  CapabilityStatus.meet_idempotent status

theorem CapabilityStatus.meet_isBelow_left
    (statusA statusB : CapabilityStatus) :
    (statusA.meet statusB).isBelow statusA := by
  cases statusA <;> cases statusB <;> rfl

theorem CapabilityStatus.meet_isBelow_right
    (statusA statusB : CapabilityStatus) :
    (statusA.meet statusB).isBelow statusB := by
  cases statusA <;> cases statusB <;> rfl

theorem CapabilityStatus.isBelow_trans
    {statusA statusB statusC : CapabilityStatus}
    (belowAB : statusA.isBelow statusB)
    (belowBC : statusB.isBelow statusC) :
    statusA.isBelow statusC := by
  cases statusA <;> cases statusB <;> cases statusC <;>
    first
      | rfl
      | exact belowAB
      | exact belowBC

theorem CapabilityStatus.isBelow_antisymm
    {statusA statusB : CapabilityStatus}
    (belowAB : statusA.isBelow statusB)
    (belowBA : statusB.isBelow statusA) :
    statusA = statusB := by
  cases statusA <;> cases statusB <;>
    first
      | rfl
      | exact belowAB.symm
      | exact belowBA

/-- A status below a meet is below both factors, and conversely: the
meet is the GREATEST lower bound of the two-point status lattice. -/
theorem CapabilityStatus.isBelow_meet_iff
    (statusA statusB statusC : CapabilityStatus) :
    statusC.isBelow (statusA.meet statusB) ↔
      statusC.isBelow statusA ∧ statusC.isBelow statusB := by
  cases statusA <;> cases statusB <;> cases statusC <;>
    constructor <;> intro hyp <;>
      first
        | exact ⟨rfl, rfl⟩
        | exact rfl
        | exact ⟨rfl, hyp⟩
        | exact ⟨hyp, rfl⟩
        | exact ⟨hyp, hyp⟩
        | exact hyp.1
        | exact hyp.2

/-- An available claim below another status forces that status to be
available too — the extraction lemma the admission theorem uses. -/
theorem CapabilityStatus.eq_available_of_isBelow_of_available
    {statusA statusB : CapabilityStatus}
    (below : statusA.isBelow statusB)
    (claimed : statusA = .available) :
    statusB = .available := by
  cases statusA <;> cases statusB <;>
    first
      | rfl
      | exact claimed
      | exact below

/-- The capability-record order: componentwise `isBelow`. -/
def MetatheoreticCapabilities.isBelow
    (capA capB : MetatheoreticCapabilities) : Prop :=
  capA.canonicityStatus.isBelow capB.canonicityStatus ∧
  capA.normalizationStatus.isBelow capB.normalizationStatus ∧
  capA.parametricityStatus.isBelow capB.parametricityStatus ∧
  capA.subjectReductionStatus.isBelow capB.subjectReductionStatus ∧
  capA.confluenceStatus.isBelow capB.confluenceStatus ∧
  capA.strongNormalizationStatus.isBelow capB.strongNormalizationStatus ∧
  capA.decidableConversionStatus.isBelow capB.decidableConversionStatus ∧
  capA.decidableTypecheckingStatus.isBelow capB.decidableTypecheckingStatus

instance (capA capB : MetatheoreticCapabilities) :
    Decidable (capA.isBelow capB) :=
  inferInstanceAs (Decidable
    (capA.canonicityStatus.isBelow capB.canonicityStatus ∧
     capA.normalizationStatus.isBelow capB.normalizationStatus ∧
     capA.parametricityStatus.isBelow capB.parametricityStatus ∧
     capA.subjectReductionStatus.isBelow capB.subjectReductionStatus ∧
     capA.confluenceStatus.isBelow capB.confluenceStatus ∧
     capA.strongNormalizationStatus.isBelow
       capB.strongNormalizationStatus ∧
     capA.decidableConversionStatus.isBelow
       capB.decidableConversionStatus ∧
     capA.decidableTypecheckingStatus.isBelow
       capB.decidableTypecheckingStatus))

theorem MetatheoreticCapabilities.isBelow_refl
    (cap : MetatheoreticCapabilities) :
    cap.isBelow cap :=
  ⟨CapabilityStatus.isBelow_refl _, CapabilityStatus.isBelow_refl _,
   CapabilityStatus.isBelow_refl _, CapabilityStatus.isBelow_refl _,
   CapabilityStatus.isBelow_refl _, CapabilityStatus.isBelow_refl _,
   CapabilityStatus.isBelow_refl _, CapabilityStatus.isBelow_refl _⟩

/-- (T3 lattice law) The meet is below its left factor. -/
theorem MetatheoreticCapabilities.meet_isBelow_left
    (capA capB : MetatheoreticCapabilities) :
    (capA.meet capB).isBelow capA :=
  ⟨CapabilityStatus.meet_isBelow_left _ _,
   CapabilityStatus.meet_isBelow_left _ _,
   CapabilityStatus.meet_isBelow_left _ _,
   CapabilityStatus.meet_isBelow_left _ _,
   CapabilityStatus.meet_isBelow_left _ _,
   CapabilityStatus.meet_isBelow_left _ _,
   CapabilityStatus.meet_isBelow_left _ _,
   CapabilityStatus.meet_isBelow_left _ _⟩

/-- (T3 lattice law) The meet is below its right factor. -/
theorem MetatheoreticCapabilities.meet_isBelow_right
    (capA capB : MetatheoreticCapabilities) :
    (capA.meet capB).isBelow capB :=
  ⟨CapabilityStatus.meet_isBelow_right _ _,
   CapabilityStatus.meet_isBelow_right _ _,
   CapabilityStatus.meet_isBelow_right _ _,
   CapabilityStatus.meet_isBelow_right _ _,
   CapabilityStatus.meet_isBelow_right _ _,
   CapabilityStatus.meet_isBelow_right _ _,
   CapabilityStatus.meet_isBelow_right _ _,
   CapabilityStatus.meet_isBelow_right _ _⟩

theorem MetatheoreticCapabilities.isBelow_trans
    {capA capB capC : MetatheoreticCapabilities}
    (belowAB : capA.isBelow capB)
    (belowBC : capB.isBelow capC) :
    capA.isBelow capC :=
  ⟨CapabilityStatus.isBelow_trans belowAB.1 belowBC.1,
   CapabilityStatus.isBelow_trans belowAB.2.1 belowBC.2.1,
   CapabilityStatus.isBelow_trans belowAB.2.2.1 belowBC.2.2.1,
   CapabilityStatus.isBelow_trans belowAB.2.2.2.1 belowBC.2.2.2.1,
   CapabilityStatus.isBelow_trans belowAB.2.2.2.2.1 belowBC.2.2.2.2.1,
   CapabilityStatus.isBelow_trans belowAB.2.2.2.2.2.1 belowBC.2.2.2.2.2.1,
   CapabilityStatus.isBelow_trans
     belowAB.2.2.2.2.2.2.1 belowBC.2.2.2.2.2.2.1,
   CapabilityStatus.isBelow_trans
     belowAB.2.2.2.2.2.2.2 belowBC.2.2.2.2.2.2.2⟩

/-- (T3 universal property) The meet is the GREATEST lower bound:
anything below both factors is below the meet. -/
theorem MetatheoreticCapabilities.isBelow_meet_of_isBelow_both
    {capA capB capC : MetatheoreticCapabilities}
    (belowA : capC.isBelow capA)
    (belowB : capC.isBelow capB) :
    capC.isBelow (capA.meet capB) :=
  ⟨(CapabilityStatus.isBelow_meet_iff _ _ _).mpr ⟨belowA.1, belowB.1⟩,
   (CapabilityStatus.isBelow_meet_iff _ _ _).mpr ⟨belowA.2.1, belowB.2.1⟩,
   (CapabilityStatus.isBelow_meet_iff _ _ _).mpr
     ⟨belowA.2.2.1, belowB.2.2.1⟩,
   (CapabilityStatus.isBelow_meet_iff _ _ _).mpr
     ⟨belowA.2.2.2.1, belowB.2.2.2.1⟩,
   (CapabilityStatus.isBelow_meet_iff _ _ _).mpr
     ⟨belowA.2.2.2.2.1, belowB.2.2.2.2.1⟩,
   (CapabilityStatus.isBelow_meet_iff _ _ _).mpr
     ⟨belowA.2.2.2.2.2.1, belowB.2.2.2.2.2.1⟩,
   (CapabilityStatus.isBelow_meet_iff _ _ _).mpr
     ⟨belowA.2.2.2.2.2.2.1, belowB.2.2.2.2.2.2.1⟩,
   (CapabilityStatus.isBelow_meet_iff _ _ _).mpr
     ⟨belowA.2.2.2.2.2.2.2, belowB.2.2.2.2.2.2.2⟩⟩

end FX1Poly.Tier0

namespace FX1Poly.Extension

open Core Tier0

/-! ## AdmissibleProfile — the ledger-backed admission predicate

The honest semantics: a profile is ledger-admissible when the
capability record it advertises is BACKED by the profile's own
construction ledgers.  Claiming nothing (`bot`) is free; claiming a
capability requires the matching `has<X> = true` flag on the profile.
This is deliberately the WEAK reading — it transfers bookkeeping, not
theorems.  The strong reading is `FullAdmissionObligations` below. -/

structure AdmissibleProfile (profile : PolyProfile) where
  /-- The capability record this admission claims for the profile. -/
  capabilities : MetatheoreticCapabilities
  /-- A canonicity claim must be backed by the Axis 12 STC ledger. -/
  canonicityBacked :
    capabilities.canonicityStatus = .available →
      profile.stcConstructionLevel.hasCanonicityTheorem = true
  /-- A normalization claim must be backed by the Axis 12 STC ledger. -/
  normalizationBacked :
    capabilities.normalizationStatus = .available →
      profile.stcConstructionLevel.hasNormalizationTheorem = true
  /-- A decidable-conversion claim must be backed by the Axis 13 ledger. -/
  decidableConversionBacked :
    capabilities.decidableConversionStatus = .available →
      profile.mttNormConstructionLevel.hasFXConversionDecidableTheorem =
        true

/-- Every profile is ledger-admissible at the bottom capability record:
claiming nothing requires no backing.  This is the honest floor, not a
metatheory result. -/
def AdmissibleProfile.bottom (profile : PolyProfile) :
    AdmissibleProfile profile where
  capabilities := MetatheoreticCapabilities.bot
  canonicityBacked := fun claimed => CapabilityStatus.noConfusion claimed
  normalizationBacked := fun claimed => CapabilityStatus.noConfusion claimed
  decidableConversionBacked := fun claimed =>
    CapabilityStatus.noConfusion claimed

/-- The FX profile is ledger-admissible at bottom — claiming nothing
requires no backing.  Retained as the conservative floor; since the
SN-100 canonicity flip, bottom is no longer the ONLY admission the
ledger discipline permits (see `fxProfileCanonicityAdmission`). -/
def fxProfileLedgerAdmission : AdmissibleProfile fxProfile :=
  AdmissibleProfile.bottom fxProfile

theorem fxProfileLedgerAdmission_capabilities_eq_bot :
    fxProfileLedgerAdmission.capabilities =
      MetatheoreticCapabilities.bot := rfl

/-- The first NON-BOTTOM ledger admission for FX: the canonicity claim
is now backable — `fxProfile`'s STC ledger carries the bool canonicity
theorem (`canonicityViaSTC`, SN-100), so `hasCanonicityTheorem = true`
discharges `canonicityBacked`.  Normalization and decidable-conversion
stay unclaimed (their ledger rungs are still false). -/
def fxProfileCanonicityAdmission : AdmissibleProfile fxProfile where
  capabilities :=
    { MetatheoreticCapabilities.bot with canonicityStatus := .available }
  canonicityBacked := fun _ => fxProfile_stcHasCanonicityTheorem
  normalizationBacked := fun claimed => CapabilityStatus.noConfusion claimed
  decidableConversionBacked := fun claimed =>
    CapabilityStatus.noConfusion claimed

/-- The non-bottom admission genuinely claims canonicity. -/
theorem fxProfileCanonicityAdmission_claims_canonicity :
    fxProfileCanonicityAdmission.capabilities.canonicityStatus =
      CapabilityStatus.available := rfl

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
statement no longer distinguishes the two.  Restating the field to
require advancement (and deciding whether `FullAdmissionObligations`
should then be inhabited) is the `admissibleProfileTheorem`-rung
decision (SN-108), deliberately NOT taken here. -/
theorem fullAdmission_metatheoryRealized_canonicityRung_dischargeable
    (extension : ProfileExtension fxProfile) :
    (extendProfile fxProfile
        extension).stcConstructionLevel.hasCanonicityTheorem = true := by
  rw [extendProfile_preserves_stcConstructionLevel]
  exact fxProfile_stcHasCanonicityTheorem

/-! ## Cellular tensor (T1)-(T3) obligation shapes (#217)

polycell.md §3.0.7: the tensor of two admissible profiles.  (T1)
construction (Almeida vol I GAT tensor + re-stratification) and (T2)
admissibility preservation (BKS sconing composition) are the open
research program — they appear here only as fields of the obligation
record.  (T3) is the capability-meet honesty ledger: its LATTICE
content (meet is the decidable greatest lower bound) is proved above;
its per-tensor content is the `capabilitiesBound` field.  (T4)-(T8)
are out of scope (no ProfileMorphism category exists in the tree). -/

structure CellularTensorObligations
    (profileA profileB : PolyProfile) where
  /-- (T1) The tensor profile: Almeida vol I syntactic GAT tensor of
  the two profiles' GAT shadows, re-stratified by the FX cell-sort
  enumeration.  No algorithm for this exists in the tree. -/
  tensorProfile : PolyProfile
  /-- (T2) Admissibility preservation via BKS internal-sconing
  composition: both factors' admissions compose to an admission of
  the tensor. -/
  admissibilityPreserved :
    AdmissibleProfile profileA → AdmissibleProfile profileB →
      AdmissibleProfile tensorProfile
  /-- (T3) Capability honesty ledger: the tensor's capability record
  is AT MOST the meet of the factors' records (upper bound, per the
  polycell.md normative prose — NOT the sketch's equality, and NOT a
  substitute for per-pair interaction proofs). -/
  capabilitiesBound :
    ∀ (admissionA : AdmissibleProfile profileA)
      (admissionB : AdmissibleProfile profileB),
      (admissibilityPreserved admissionA admissionB).capabilities.isBelow
        (admissionA.capabilities.meet admissionB.capabilities)

/-! ## (T7) Zwart-Marsden no-go register

A static register of published distributive-law no-go cells.  When a
tensor attempt hits a registered cell, the admission contract must
REJECT (or admit syntax-only) rather than silently degrade to lattice
bottom.  The register is data, cross-referenced against
arXiv:1811.06460; it is not a computed lattice value. -/

/-- The admission posture when a no-go cell fires. -/
inductive NoGoPosture where
  /-- The extension pair is rejected outright. -/
  | reject
  /-- The generators are admitted with NO metatheory transfer asserted. -/
  | syntaxOnly
  deriving DecidableEq, Repr

/-- One registered no-go cell: a published obstruction to composing
two effect/extension theories. -/
structure NoGoCell where
  /-- The first theory of the colliding pair. -/
  firstTheory : String
  /-- The second theory of the colliding pair. -/
  secondTheory : String
  /-- The published obstruction (theorem reference inside
  Zwart-Marsden arXiv:1811.06460 or a successor catalogue). -/
  obstruction : String
  /-- The mandated admission posture. -/
  posture : NoGoPosture
  deriving Repr

/-- The initial Zwart-Marsden register: the headline no-go cells from
arXiv:1811.06460.  Static data — extending it is editing this list,
not proving anything. -/
def zwartMarsdenRegister : List NoGoCell :=
  [{ firstTheory := "probability (convex combinations)"
     secondTheory := "powerset (nondeterminism)"
     obstruction :=
       "Zwart-Marsden arXiv:1811.06460 Thm 4.6: no distributive law"
     posture := .reject },
   { firstTheory := "probability (convex combinations)"
     secondTheory := "probability (convex combinations)"
     obstruction :=
       "Zwart-Marsden arXiv:1811.06460 Thm 5.4: no self-distribution"
     posture := .reject },
   { firstTheory := "powerset (nondeterminism)"
     secondTheory := "powerset (nondeterminism)"
     obstruction :=
       "Zwart-Marsden arXiv:1811.06460 Thm 4.8: no self-distribution"
     posture := .reject }]

theorem zwartMarsdenRegister_length : zwartMarsdenRegister.length = 3 :=
  rfl

/-- Every registered cell currently mandates rejection — no silent
degradation posture is registered. -/
theorem zwartMarsdenRegister_allReject :
    ∀ cell, cell ∈ zwartMarsdenRegister → cell.posture = .reject := by
  intro cell membership
  cases membership with
  | head => rfl
  | tail _ membershipTail =>
    cases membershipTail with
    | head => rfl
    | tail _ membershipTailTail =>
      cases membershipTailTail with
      | head => rfl
      | tail _ membershipEmpty => cases membershipEmpty

/-! ## Honesty pins

The construction-level ledger stays below the admission-theorem rung:
the ledger fragment above is `extendProfile` bookkeeping plus lattice
laws, not the §3.14 metatheory-transfer theorem, and no
`CellularTensorObligations` value exists in the tree. -/

theorem extensionLedger_stillBelow_metatheoryTransfer :
    fxExtensionConstructionLevel.hasMetatheoryTransfer = false := rfl

theorem extensionLedger_stillBelow_admissibleProfileTheorem :
    fxExtensionConstructionLevel.hasAdmissibleProfileTheorem = false := rfl

end FX1Poly.Extension
