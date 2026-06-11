import FX1Poly.Core.PolyProfile
import FX1Poly.Tier0.AxisObligation
/-! # FX1Poly/Core/ProfileAdmission — the KERNEL-NATIVE admission discipline

A profile's capability claims must be BACKED by its own construction
ledgers.  This is kernel content — it speaks only about `PolyProfile`
and the capability lattice, never about the extension PoC — and lives
here accordingly (integrated from the quarantined extension layer per
the kernel-native discipline).

  * `AdmissibleProfile` — the ledger-backed admission record: claiming
    a capability requires the matching `has<X> = true` ledger flag.
    The WEAK (bookkeeping) reading; it transfers claims, not theorems.
  * `AdmissibleProfile.bottom` / `fxProfileLedgerAdmission` — the
    claim-nothing floor, free for every profile.
  * `fxProfileCanonicityAdmission` / `fxProfileMetatheoryAdmission` —
    the non-bottom FX admissions, backed by the Axis 12 STC ledger
    rungs (`canonicityViaSTC`, `normalizationViaSTC`).
  * `AdmissibleProfile.meetAdmission` — two admissions of one profile
    meet; the meet capability record is backed because each
    meet-available claim is already available in the first admission.
  * `CellularTensorObligations` + `diagonalCellularTensor` — the
    polycell.md §3.0.7 (T1)-(T3) obligation shape and its degenerate
    DIAGONAL inhabitant (same-profile tensor via the meet admission,
    the (T3) bound attained by reflexivity).  Heterogeneous (T1)/(T2)
    — realized GAT tensor + BKS sconing composition — remain the open
    research program; no heterogeneous instance exists.
  * The (T7) Zwart-Marsden no-go register + its computable symmetric
    gate (`findNoGoCell` + soundness): a tensor attempt hitting a
    registered cell must REJECT, never silently degrade.

Zero-axiom; gated in `FX1PolyAudit/AuditProfile.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Tier0

/-! ## AdmissibleProfile — the ledger-backed admission predicate -/

/-- The honest semantics: a profile is ledger-admissible when the
capability record it advertises is BACKED by the profile's own
construction ledgers.  Claiming nothing (`bot`) is free; claiming a
capability requires the matching `has<X> = true` flag on the profile.
This is deliberately the WEAK reading — it transfers bookkeeping, not
theorems. -/
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
canonicity ledger flip, bottom is no longer the ONLY admission the
ledger discipline permits (see `fxProfileCanonicityAdmission`). -/
def fxProfileLedgerAdmission : AdmissibleProfile fxProfile :=
  AdmissibleProfile.bottom fxProfile

theorem fxProfileLedgerAdmission_capabilities_eq_bot :
    fxProfileLedgerAdmission.capabilities =
      MetatheoreticCapabilities.bot := rfl

/-- The first NON-BOTTOM ledger admission for FX: the canonicity claim
is backable — `fxProfile`'s STC ledger carries the bool canonicity
theorem (`canonicityViaSTC`), so `hasCanonicityTheorem = true`
discharges `canonicityBacked`.  Normalization is backable too (see
`fxProfileMetatheoryAdmission`); decidable-conversion stays unclaimed
(the Axis 13 rung is still false). -/
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

/-- The ledger admission claiming BOTH canonicity and normalization —
both Axis 12 rungs are true (`canonicityViaSTC`,
`normalizationViaSTC`).  Decidable-conversion stays unclaimed (its
backing is the Axis 13 `hasFXConversionDecidableTheorem` rung, still
false). -/
def fxProfileMetatheoryAdmission : AdmissibleProfile fxProfile where
  capabilities :=
    { MetatheoreticCapabilities.bot with
        canonicityStatus := .available
        normalizationStatus := .available }
  canonicityBacked := fun _ => fxProfile_stcHasCanonicityTheorem
  normalizationBacked := fun _ => fxProfile_stcHasNormalizationTheorem
  decidableConversionBacked := fun claimed =>
    CapabilityStatus.noConfusion claimed

/-- The metatheory admission genuinely claims both rungs. -/
theorem fxProfileMetatheoryAdmission_claims_both :
    fxProfileMetatheoryAdmission.capabilities.canonicityStatus =
        CapabilityStatus.available ∧
      fxProfileMetatheoryAdmission.capabilities.normalizationStatus =
        CapabilityStatus.available :=
  ⟨rfl, rfl⟩

/-- Two ledger admissions of the SAME profile meet: the meet
capability record is backed because each meet-available claim is
already available in (and backed by) the first admission. -/
def AdmissibleProfile.meetAdmission {profile : PolyProfile}
    (admissionA admissionB : AdmissibleProfile profile) :
    AdmissibleProfile profile where
  capabilities := admissionA.capabilities.meet admissionB.capabilities
  canonicityBacked := fun claimed =>
    admissionA.canonicityBacked
      (CapabilityStatus.eq_available_of_isBelow_of_available
        (MetatheoreticCapabilities.meet_isBelow_left
          admissionA.capabilities admissionB.capabilities).1
        claimed)
  normalizationBacked := fun claimed =>
    admissionA.normalizationBacked
      (CapabilityStatus.eq_available_of_isBelow_of_available
        (MetatheoreticCapabilities.meet_isBelow_left
          admissionA.capabilities admissionB.capabilities).2.1
        claimed)
  decidableConversionBacked := fun claimed =>
    admissionA.decidableConversionBacked
      (CapabilityStatus.eq_available_of_isBelow_of_available
        (MetatheoreticCapabilities.meet_isBelow_left
          admissionA.capabilities admissionB.capabilities).2.2.2.2.2.2.1
        claimed)

/-! ## Cellular tensor (T1)-(T3) obligation shapes

polycell.md §3.0.7: the tensor of two admissible profiles.  (T1)
construction (Almeida vol I GAT tensor + re-stratification) and (T2)
admissibility preservation (BKS sconing composition) are the open
research program — they appear here as fields of the obligation
record; only the degenerate DIAGONAL inhabitant exists. -/

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

/-- ★ The FIRST `CellularTensorObligations` inhabitant: the DIAGONAL
instance.  Tensor of a profile with itself is the profile;
admissibility composes by the meet admission; the (T3) bound is
reflexivity (the bound is attained exactly).  Degenerate by design —
it pins that the obligation shape is coherent, while heterogeneous
(T1)/(T2) stay open. -/
def diagonalCellularTensor (profile : PolyProfile) :
    CellularTensorObligations profile profile where
  tensorProfile := profile
  admissibilityPreserved := AdmissibleProfile.meetAdmission
  capabilitiesBound := fun admissionA admissionB =>
    MetatheoreticCapabilities.isBelow_refl
      (admissionA.capabilities.meet admissionB.capabilities)

/-- Non-vacuity smoke on FX: the diagonal tensor of the two shipped
non-bottom admissions (canonicity-only ⊓ canonicity+normalization)
carries exactly the canonicity-only capability record. -/
theorem diagonalTensor_fx_meetCapabilities :
    ((diagonalCellularTensor fxProfile).admissibilityPreserved
        fxProfileCanonicityAdmission fxProfileMetatheoryAdmission).capabilities
      = fxProfileCanonicityAdmission.capabilities := rfl

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

/-! ## The (T7) admission gate — computable register lookup

The register is static data; the GATE is the computable lookup a
tensor-admission contract consults: symmetric in the pair (a tensor
attempt may present the theories in either order), sound (a hit is a
registered cell, and every registered cell mandates rejection). -/

/-- Does this cell match the (unordered) theory pair? -/
def NoGoCell.matchesPair (cell : NoGoCell)
    (theoryA theoryB : String) : Bool :=
  (cell.firstTheory == theoryA && cell.secondTheory == theoryB) ||
    (cell.firstTheory == theoryB && cell.secondTheory == theoryA)

/-- Find the first registered cell matching the unordered theory
pair. -/
def findNoGoCell (theoryA theoryB : String) :
    List NoGoCell → Option NoGoCell
  | [] => none
  | cell :: rest =>
    match cell.matchesPair theoryA theoryB with
    | true => some cell
    | false => findNoGoCell theoryA theoryB rest

/-- Lookup soundness: a hit is a member of the searched register. -/
theorem findNoGoCell_mem (theoryA theoryB : String) :
    (cells : List NoGoCell) → {cell : NoGoCell} →
      findNoGoCell theoryA theoryB cells = some cell → cell ∈ cells
  | [], _, found => nomatch found
  | headCell :: rest, cell, found => by
    dsimp only [findNoGoCell] at found
    cases matchTest : headCell.matchesPair theoryA theoryB with
    | true =>
      rw [matchTest] at found
      have headEqCell : headCell = cell := Option.some.inj found
      cases headEqCell
      exact List.Mem.head rest
    | false =>
      rw [matchTest] at found
      exact List.Mem.tail headCell
        (findNoGoCell_mem theoryA theoryB rest found)

/-- ★ Gate soundness on the shipped register: every hit mandates
REJECTION — the admission contract cannot silently degrade. -/
theorem findNoGoCell_register_posture {theoryA theoryB : String}
    {cell : NoGoCell}
    (found : findNoGoCell theoryA theoryB zwartMarsdenRegister
      = some cell) :
    cell.posture = NoGoPosture.reject :=
  zwartMarsdenRegister_allReject cell
    (findNoGoCell_mem theoryA theoryB zwartMarsdenRegister found)

/-- The probability⊗powerset tensor attempt HITS the register. -/
theorem probabilityPowersetTensor_isRejected :
    (findNoGoCell "probability (convex combinations)"
        "powerset (nondeterminism)" zwartMarsdenRegister).isSome
      = true := rfl

/-- The SYMMETRIC presentation also hits — the gate is unordered. -/
theorem powersetProbabilityTensor_isRejected :
    (findNoGoCell "powerset (nondeterminism)"
        "probability (convex combinations)" zwartMarsdenRegister).isSome
      = true := rfl

/-- An unregistered pair passes the gate (the register constrains, it
does not blanket-reject). -/
theorem unregisteredTensorPair_passesGate :
    (findNoGoCell "exceptions" "global state"
        zwartMarsdenRegister).isSome = false := rfl

end FX1Poly.Core
