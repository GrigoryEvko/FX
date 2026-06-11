import FX1PolyAudit.AuditGen
import FX1Poly.Core.PolyProfile
import FX1Poly.Tier0.InternalSconing
import FX1Poly.Tier0.FireTriangle
import FX1Poly.Extension.ProfileExtension
import FX1Poly.Extension.AdmissibleProfileTensor
import FX1Poly.Extension.FxWithEtaCertifier
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
#assert_namespace_min_count FX1Poly.Algebra 114
#audit_namespace FX1Poly.Enrichment
#assert_namespace_min_count FX1Poly.Enrichment 90
#audit_namespace FX1Poly.Gray
#assert_namespace_min_count FX1Poly.Gray 29
#audit_namespace FX1Poly.MTTNorm
#assert_namespace_min_count FX1Poly.MTTNorm 130
#audit_namespace FX1Poly.Modal
#assert_namespace_min_count FX1Poly.Modal 106
#audit_namespace FX1Poly.OmegacE
#assert_namespace_min_count FX1Poly.OmegacE 124
#audit_namespace FX1Poly.ProfileFibration
#assert_namespace_min_count FX1Poly.ProfileFibration 72
#audit_namespace FX1Poly.SSC
#assert_namespace_min_count FX1Poly.SSC 30
#audit_namespace FX1Poly.STC
#assert_namespace_min_count FX1Poly.STC 95
#audit_namespace FX1Poly.Saturation
#assert_namespace_min_count FX1Poly.Saturation 122
#audit_namespace FX1Poly.Shape
#assert_namespace_min_count FX1Poly.Shape 95
#audit_namespace FX1Poly.Stratification
#assert_namespace_min_count FX1Poly.Stratification 93
#audit_namespace FX1Poly.Tier0
#assert_namespace_min_count FX1Poly.Tier0 439
#audit_namespace FX1Poly.Extension
#assert_namespace_min_count FX1Poly.Extension 203

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

/-! ## fxWithEta-through-the-certifier gates (V2-L5.4)

The first end-to-end profile-extension demonstration on the canonical
kernel: profile-uniform corpus certification (the certifier never
reads the profile), fxWithEta instances including a dim-1 cell, the
declared eta rules discharged against the kernel SR-eta arms at the
extended profile, and a concrete eta-pair step run end-to-end. -/

#assert_no_axioms FX1Poly.Extension.unitLeafTerm
#assert_no_axioms FX1Poly.Extension.unitPairTerm
#assert_no_axioms FX1Poly.Extension.certified_unitLeaf_uniform
#assert_no_axioms FX1Poly.Extension.certified_unitPair_uniform
#assert_no_axioms FX1Poly.Extension.certified_etaPairSource_uniform
#assert_no_axioms FX1Poly.Extension.fxWithEta_certifies_unitLeaf
#assert_no_axioms FX1Poly.Extension.fxWithEta_certifies_unitPair
#assert_no_axioms FX1Poly.Extension.fxWithEta_certifies_etaPairSource
#assert_no_axioms FX1Poly.Extension.fxWithEta_certifies_identityCell
#assert_no_axioms
  FX1Poly.Extension.EtaReductionRule.preservesCertificationAt
#assert_no_axioms
  FX1Poly.Extension.EtaReductionRule.fxWithEta_preservesCertification
#assert_no_axioms FX1Poly.Extension.etaPairStep_fires_on_unitPair
#assert_no_axioms
  FX1Poly.Extension.fxWithEta_etaPairSource_hasCertifiedCell
#assert_no_axioms
  FX1Poly.Extension.fxWithEta_etaPairTarget_certified_viaSR
#assert_no_axioms FX1Poly.Extension.fxWithEta_fibrationTower_eq
#assert_no_axioms FX1Poly.Extension.fxWithEta_algebraUniverse_eq
#assert_no_axioms FX1Poly.Extension.fxWithEta_universeConfig_eq
