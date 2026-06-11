import FX1PolyAudit.AuditGen
import FX1Poly.Core.PolyProfile
import FX1Poly.Tier0.InternalSconing
import FX1Poly.Tier0.FireTriangle
import FX1Poly.Extension.ProfileExtension
import FX1Poly.Extension.AdmissibleProfileTensor
import FX1Poly.Core.StrengthCalibration

/-! # FX1PolyAudit/AuditProfile — namespace zero-axiom sweep for the axis substrate

Persistent zero-axiom gate for the PolyProfile axis closure.  `PolyProfile`
bundles the fourteen graded-modal axis structures the cell calculus
fibres over (the directed-complex shape, univalent algebra, thin
stratification, cubical saturation, rung enrichment, Gray tensor,
cohesive-focus modality, profile-fibration morphisms, omega-c-enriched
hom, SSC backbone, STC modalities, MTT mode theory, universe config).

Each axis file is self-contained (no Core / native-infra / MLTT
dependency).  The `#audit_namespace` sweeps walk every loaded
declaration under each axis namespace and fail the build at the first
axiom leak.
-/

#audit_namespace FX1Poly.Algebra
#audit_namespace FX1Poly.Enrichment
#audit_namespace FX1Poly.Gray
#audit_namespace FX1Poly.MTTNorm
#audit_namespace FX1Poly.Modal
#audit_namespace FX1Poly.OmegacE
#audit_namespace FX1Poly.ProfileFibration
#audit_namespace FX1Poly.SSC
#audit_namespace FX1Poly.STC
#audit_namespace FX1Poly.Saturation
#audit_namespace FX1Poly.Shape
#audit_namespace FX1Poly.Stratification
#audit_namespace FX1Poly.Tier0
#audit_namespace FX1Poly.Extension

/-! ## AdmissibleProfile + cellular tensor headline gates

Explicit per-declaration gates for the ledger admission theorem, the
capability lattice laws backing the (T3) honesty ledger, the full
admission / cellular tensor obligation SHAPES, and the Zwart-Marsden
no-go register. -/

#assert_no_axioms FX1Poly.Tier0.CapabilityStatus.isBelow_refl
#assert_no_axioms FX1Poly.Tier0.CapabilityStatus.meet_isBelow_left
#assert_no_axioms FX1Poly.Tier0.CapabilityStatus.meet_isBelow_right
#assert_no_axioms FX1Poly.Tier0.CapabilityStatus.isBelow_trans
#assert_no_axioms FX1Poly.Tier0.CapabilityStatus.isBelow_antisymm
#assert_no_axioms FX1Poly.Tier0.CapabilityStatus.isBelow_meet_iff
#assert_no_axioms
  FX1Poly.Tier0.CapabilityStatus.eq_available_of_isBelow_of_available
#assert_no_axioms FX1Poly.Tier0.MetatheoreticCapabilities.isBelow_refl
#assert_no_axioms FX1Poly.Tier0.MetatheoreticCapabilities.meet_isBelow_left
#assert_no_axioms FX1Poly.Tier0.MetatheoreticCapabilities.meet_isBelow_right
#assert_no_axioms FX1Poly.Tier0.MetatheoreticCapabilities.isBelow_trans
#assert_no_axioms
  FX1Poly.Tier0.MetatheoreticCapabilities.isBelow_meet_of_isBelow_both
#assert_no_axioms FX1Poly.Extension.AdmissibleProfile
#assert_no_axioms FX1Poly.Extension.AdmissibleProfile.bottom
#assert_no_axioms FX1Poly.Extension.fxProfileLedgerAdmission
#assert_no_axioms
  FX1Poly.Extension.fxProfileLedgerAdmission_capabilities_eq_bot
#assert_no_axioms FX1Poly.Extension.extendProfile_preserves_admissible
#assert_no_axioms
  FX1Poly.Extension.extendProfile_preserves_admissible_capabilities
#assert_no_axioms FX1Poly.Extension.fxWithEta_admission_capabilities_eq_bot
#assert_no_axioms FX1Poly.Extension.FullAdmissionObligations
#assert_no_axioms
  FX1Poly.Extension.fullAdmission_metatheoryRealized_unrealizable_for_fx
#assert_no_axioms FX1Poly.Extension.CellularTensorObligations
#assert_no_axioms FX1Poly.Extension.NoGoPosture
#assert_no_axioms FX1Poly.Extension.NoGoCell
#assert_no_axioms FX1Poly.Extension.zwartMarsdenRegister
#assert_no_axioms FX1Poly.Extension.zwartMarsdenRegister_length
#assert_no_axioms FX1Poly.Extension.zwartMarsdenRegister_allReject
#assert_no_axioms
  FX1Poly.Extension.extensionLedger_stillBelow_metatheoryTransfer
#assert_no_axioms
  FX1Poly.Extension.extensionLedger_stillBelow_admissibleProfileTheorem

/-! ## Strength-calibration gates (one canonical strength enum)

`FX1Poly.Core.ConsistencyStrength` is the canonical strength enum;
the UniverseFlag ladder and the Tier-0 ledger tags calibrate into it
monotonically as lower bounds. -/

#assert_no_axioms FX1Poly.Universe.UniverseFlag.ladderRank
#assert_no_axioms FX1Poly.Universe.UniverseFlag.consistencyStrengthBound
#assert_no_axioms
  FX1Poly.Universe.UniverseFlag.consistencyStrengthBound_monotone
#assert_no_axioms
  FX1Poly.Universe.UniverseFlag.standard_calibratesTo_predicative
#assert_no_axioms FX1Poly.Universe.UniverseFlag.mahlo_calibratesTo_mahlo
#assert_no_axioms
  FX1Poly.Universe.UniverseFlag.vopenka_calibratesTo_customZero
#assert_no_axioms FX1Poly.Tier0.ConsistencyStrength.rank
#assert_no_axioms FX1Poly.Tier0.ConsistencyStrength.toCoreStrength
#assert_no_axioms FX1Poly.Tier0.ConsistencyStrength.toCoreStrength_monotone
#assert_no_axioms
  FX1Poly.Tier0.ConsistencyStrength.toCoreStrength_not_injective
