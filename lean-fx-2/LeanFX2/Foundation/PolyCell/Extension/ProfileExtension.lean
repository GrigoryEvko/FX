import LeanFX2.Foundation.PolyCell.Core.PolyTerm
import LeanFX2.Foundation.PolyCell.Tier0.AxisObligation
/-!
# ProfileExtension — The Current Admission Ledger (§3.14)

A ProfileExtension is the mechanism by which new features are intended
to be added to FX without cascade. This file currently mechanizes the
small proof-relevant admission ledger and the profile-tower bookkeeping.

New features should eventually be admitted profile extensions with
per-extension interaction-law and metatheory-preservation witnesses.  The
present file has not reached that theorem: it records a narrow local
ledger, preserves several construction-level fields by definitional
projection, and adds one finite node to the profile tower.

Reference: polycell.md §3.14, arXiv:2604.01303.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Extension

open Core Tier0

/-- A construction-level ledger for the current profile-extension subsystem.

The order is intentional: later milestones may use the earlier interfaces,
but this file only reaches profile-tower bookkeeping. -/
inductive ExtensionConstructionLevel where
  | interfaceLedger
  | localAdmissionRecord
  | profileTowerBookkeeping
  | profileLensInstance
  | algebraExtension
  | interactionLawProofs
  | metatheoryTransfer
  | admissibleProfileTheorem
  deriving DecidableEq, Repr

def ExtensionConstructionLevel.hasInterfaceLedger :
    ExtensionConstructionLevel → Bool
  | .interfaceLedger => true
  | .localAdmissionRecord => true
  | .profileTowerBookkeeping => true
  | .profileLensInstance => true
  | .algebraExtension => true
  | .interactionLawProofs => true
  | .metatheoryTransfer => true
  | .admissibleProfileTheorem => true

def ExtensionConstructionLevel.hasLocalAdmissionRecord :
    ExtensionConstructionLevel → Bool
  | .interfaceLedger => false
  | .localAdmissionRecord => true
  | .profileTowerBookkeeping => true
  | .profileLensInstance => true
  | .algebraExtension => true
  | .interactionLawProofs => true
  | .metatheoryTransfer => true
  | .admissibleProfileTheorem => true

def ExtensionConstructionLevel.hasProfileTowerBookkeeping :
    ExtensionConstructionLevel → Bool
  | .interfaceLedger => false
  | .localAdmissionRecord => false
  | .profileTowerBookkeeping => true
  | .profileLensInstance => true
  | .algebraExtension => true
  | .interactionLawProofs => true
  | .metatheoryTransfer => true
  | .admissibleProfileTheorem => true

def ExtensionConstructionLevel.hasProfileLensInstance :
    ExtensionConstructionLevel → Bool
  | .interfaceLedger => false
  | .localAdmissionRecord => false
  | .profileTowerBookkeeping => false
  | .profileLensInstance => true
  | .algebraExtension => true
  | .interactionLawProofs => true
  | .metatheoryTransfer => true
  | .admissibleProfileTheorem => true

def ExtensionConstructionLevel.hasAlgebraExtension :
    ExtensionConstructionLevel → Bool
  | .interfaceLedger => false
  | .localAdmissionRecord => false
  | .profileTowerBookkeeping => false
  | .profileLensInstance => false
  | .algebraExtension => true
  | .interactionLawProofs => true
  | .metatheoryTransfer => true
  | .admissibleProfileTheorem => true

def ExtensionConstructionLevel.hasInteractionLawProofs :
    ExtensionConstructionLevel → Bool
  | .interfaceLedger => false
  | .localAdmissionRecord => false
  | .profileTowerBookkeeping => false
  | .profileLensInstance => false
  | .algebraExtension => false
  | .interactionLawProofs => true
  | .metatheoryTransfer => true
  | .admissibleProfileTheorem => true

def ExtensionConstructionLevel.hasMetatheoryTransfer :
    ExtensionConstructionLevel → Bool
  | .interfaceLedger => false
  | .localAdmissionRecord => false
  | .profileTowerBookkeeping => false
  | .profileLensInstance => false
  | .algebraExtension => false
  | .interactionLawProofs => false
  | .metatheoryTransfer => true
  | .admissibleProfileTheorem => true

def ExtensionConstructionLevel.hasAdmissibleProfileTheorem :
    ExtensionConstructionLevel → Bool
  | .interfaceLedger => false
  | .localAdmissionRecord => false
  | .profileTowerBookkeeping => false
  | .profileLensInstance => false
  | .algebraExtension => false
  | .interactionLawProofs => false
  | .metatheoryTransfer => false
  | .admissibleProfileTheorem => true

/-- Present status: interface records, local admission records, and finite
profile-tower bookkeeping.  No profile lens, algebra extension, interaction
law proof, or metatheory transfer is claimed. -/
def fxExtensionConstructionLevel : ExtensionConstructionLevel :=
  .profileTowerBookkeeping

theorem fxExtensionConstructionLevel_eq :
    fxExtensionConstructionLevel = .profileTowerBookkeeping := rfl

theorem fxExtension_hasInterfaceLedger :
    fxExtensionConstructionLevel.hasInterfaceLedger = true := rfl

theorem fxExtension_hasLocalAdmissionRecord :
    fxExtensionConstructionLevel.hasLocalAdmissionRecord = true := rfl

theorem fxExtension_hasProfileTowerBookkeeping :
    fxExtensionConstructionLevel.hasProfileTowerBookkeeping = true := rfl

theorem fxExtension_hasNoProfileLensInstance :
    fxExtensionConstructionLevel.hasProfileLensInstance = false := rfl

theorem fxExtension_hasNoAlgebraExtension :
    fxExtensionConstructionLevel.hasAlgebraExtension = false := rfl

theorem fxExtension_hasNoInteractionLawProofs :
    fxExtensionConstructionLevel.hasInteractionLawProofs = false := rfl

theorem fxExtension_hasNoMetatheoryTransfer :
    fxExtensionConstructionLevel.hasMetatheoryTransfer = false := rfl

theorem fxExtension_hasNoAdmissibleProfileTheorem :
    fxExtensionConstructionLevel.hasAdmissibleProfileTheorem = false := rfl

/-- A polynomial interface: generators and reduction rules added by an
extension.  The arity functions keep the current ledger computational instead
of recording only summary counts. -/
structure PolynomialInterface where
  /-- Number of new generators (new term/type constructors). -/
  generatorCount : Nat
  /-- Arity per new generator (how many children each takes). -/
  arities : Fin generatorCount → Nat
  /-- Number of new reduction rules. -/
  reductionCount : Nat
  /-- Arity per new reduction rule. -/
  reductionArities : Fin reductionCount → Nat

/-
Intended eight-projection record shape for a feature extension.

Per polycell.md §3.14, these fields should eventually be projections of
one categorical object. This file currently stores only the computable
ledger fields and metadata needed by the present scaffold.
-/

/-- The first eta-reduction slot when an interface has exactly two reduction
rules. -/
def etaLamReductionIndex {interface : PolynomialInterface}
    (reductionCount_eq_two : interface.reductionCount = 2) :
    Fin interface.reductionCount :=
  ⟨0, by
    rw [reductionCount_eq_two]
    decide⟩

/-- The second eta-reduction slot when an interface has exactly two reduction
rules. -/
def etaPathReductionIndex {interface : PolynomialInterface}
    (reductionCount_eq_two : interface.reductionCount = 2) :
    Fin interface.reductionCount :=
  ⟨1, by
    rw [reductionCount_eq_two]
    decide⟩

/-- The two eta-reduction rules represented by the demonstration extension.

This is only the finite rule namespace for bookkeeping.  It does not provide
operational reduction shapes or any eta metatheory. -/
inductive EtaReductionRule where
  /-- Eta for lambda terms. -/
  | etaLam
  /-- Eta for path abstractions. -/
  | etaPath
  deriving DecidableEq, Repr

/-- Canonical two-slot index for eta-reduction rules. -/
def EtaReductionRule.toFinTwo : EtaReductionRule → Fin 2
  | .etaLam => ⟨0, by decide⟩
  | .etaPath => ⟨1, by decide⟩

/-- Interpret an eta-reduction rule as a rule index for an interface with
exactly two reduction rules. -/
def EtaReductionRule.indexFor {interface : PolynomialInterface}
    (reductionCount_eq_two : interface.reductionCount = 2) :
    EtaReductionRule → Fin interface.reductionCount
  | .etaLam => etaLamReductionIndex reductionCount_eq_two
  | .etaPath => etaPathReductionIndex reductionCount_eq_two

/-- Arity of each eta-reduction rule in the current demonstration interface. -/
def EtaReductionRule.arity : EtaReductionRule → Nat
  | .etaLam => 1
  | .etaPath => 1

/-- Interface-shape evidence for the eta-reduction demonstration extension.

Eta adds no constructors and exactly the two unary reduction rules currently
tracked by the scaffold: etaLam and etaPath. -/
structure EtaReductionInterfaceEvidence (interface : PolynomialInterface) where
  generatorCount_eq_zero : interface.generatorCount = 0
  reductionCount_eq_two : interface.reductionCount = 2
  etaLamArity_eq_one :
    interface.reductionArities
      (etaLamReductionIndex reductionCount_eq_two) = 1
  etaPathArity_eq_one :
    interface.reductionArities
      (etaPathReductionIndex reductionCount_eq_two) = 1
  ruleArity_eq_declared :
    ∀ (rule : EtaReductionRule),
      interface.reductionArities
        (rule.indexFor reductionCount_eq_two) = rule.arity

/-- Evidence that the eta demonstration surface has the declared interface
shape.  This is not a proof that an operational implementation satisfies an
external specification. -/
structure ImplementationSoundEvidence (interface : PolynomialInterface) where
  etaReductionShape : EtaReductionInterfaceEvidence interface

/-- Evidence that the eta demonstration adds no generator cases to bilax
checks.  This is not a proof of all interactions with all existing axes. -/
structure BilaxCompatibilityEvidence (interface : PolynomialInterface) where
  hasNoNewGenerators : interface.generatorCount = 0

/-- Evidence that the eta demonstration leaves the dim-0 generator count
unchanged.  A real forget/lift roundtrip lives in `ProfileLens`, not here. -/
structure ConservativityEvidence (interface : PolynomialInterface) where
  hasNoNewDim0Constructors : interface.generatorCount = 0

/-- Evidence that the eta demonstration records only eta-rule shape.  This is
not canonicity, normalization, or reducibility transfer. -/
structure MetatheoryPreservationEvidence (interface : PolynomialInterface) where
  etaReductionShape : EtaReductionInterfaceEvidence interface

/-- Evidence that the eta demonstration introduces no runtime constructors
through this interface record. -/
structure ErasurePreservationEvidence (interface : PolynomialInterface) where
  hasNoRuntimeConstructors : interface.generatorCount = 0

structure ProfileExtension (baseProfile : PolyProfile) where
  /-- (1) The polynomial interface being added (new generators). -/
  interface : PolynomialInterface

  /-- (2) Local evidence that the declared interface shape is matched. -/
  implementationEvidence : ImplementationSoundEvidence interface

  /-- (3) Local evidence for the currently represented bilax cases. -/
  bilaxCompatibilityEvidence : BilaxCompatibilityEvidence interface

  /-- (4) Local dim-0 conservativity evidence, not a roundtrip by itself. -/
  conservativityEvidence : ConservativityEvidence interface

  /-- (5) Local metatheory placeholder evidence, not transfer by itself. -/
  metatheoryPreservationEvidence : MetatheoryPreservationEvidence interface

  /-- (6) Evidence that runtime erasure is preserved. -/
  erasurePreservationEvidence : ErasurePreservationEvidence interface

  /-- (7) Fire Triangle navigation for the new feature. -/
  fireTriangleRestriction : Option FireTriangleLeg

  /-- (8) Capabilities preserved by this extension. -/
  capabilities : MetatheoreticCapabilities

/-- Record a profile extension in the profile tower.

This deliberately does not claim to extend the polynomial universe yet; the
generator-level algebra extension is a later PolyCell milestone. -/
def extendProfile (baseProfile : PolyProfile)
    (_extension : ProfileExtension baseProfile) : PolyProfile where
  shapeMaxDim := baseProfile.shapeMaxDim
  shapeConstructionLevel := baseProfile.shapeConstructionLevel
  algebraUniverse := baseProfile.algebraUniverse
  stratification := baseProfile.stratification
  stratificationConstructionLevel :=
    baseProfile.stratificationConstructionLevel
  saturationCells := baseProfile.saturationCells
  saturationConstructionLevel := baseProfile.saturationConstructionLevel
  enrichment := baseProfile.enrichment
  enrichmentConstructionLevel := baseProfile.enrichmentConstructionLevel
  grayModule := baseProfile.grayModule
  cohesiveFocusCount := baseProfile.cohesiveFocusCount
  modalConstructionLevel := baseProfile.modalConstructionLevel
  fibrationTower := .extend baseProfile.fibrationTower
  fibrationConstructionLevel := baseProfile.fibrationConstructionLevel
  omegacEDimBound := baseProfile.omegacEDimBound
  omegacEConstructionLevel := baseProfile.omegacEConstructionLevel
  universeConfig := baseProfile.universeConfig
  sscBackbone := baseProfile.sscBackbone
  stcModel := baseProfile.stcModel
  stcConstructionLevel := baseProfile.stcConstructionLevel
  modeTheory := baseProfile.modeTheory
  mttNormConstructionLevel := baseProfile.mttNormConstructionLevel

/-- The current extension bookkeeping does not manufacture Axis 1 shape
evidence.  The extended profile inherits the base construction level exactly. -/
theorem extendProfile_preserves_shapeConstructionLevel
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile) :
    (extendProfile baseProfile extension).shapeConstructionLevel =
      baseProfile.shapeConstructionLevel := rfl

/-- The current extension bookkeeping does not manufacture Axis 2 polynomial
universe evidence.  The extended profile inherits the base construction level
exactly. -/
theorem extendProfile_preserves_algebraConstructionLevel
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile) :
    (extendProfile baseProfile extension).algebraUniverse.constructionLevel =
      baseProfile.algebraUniverse.constructionLevel := rfl

/-- The current extension bookkeeping does not manufacture Axis 3
stratification evidence.  The extended profile inherits the base construction
level exactly. -/
theorem extendProfile_preserves_stratificationConstructionLevel
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile) :
    (extendProfile baseProfile extension).stratificationConstructionLevel =
      baseProfile.stratificationConstructionLevel := rfl

/-- The current extension bookkeeping does not manufacture Axis 4 saturation
evidence.  The extended profile inherits the base construction level exactly. -/
theorem extendProfile_preserves_saturationConstructionLevel
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile) :
    (extendProfile baseProfile extension).saturationConstructionLevel =
      baseProfile.saturationConstructionLevel := rfl

/-- The current extension bookkeeping does not manufacture Axis 9 classifier
evidence.  The extended profile inherits the base construction level exactly. -/
theorem extendProfile_preserves_omegacEConstructionLevel
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile) :
    (extendProfile baseProfile extension).omegacEConstructionLevel =
      baseProfile.omegacEConstructionLevel := rfl

/-- The current extension bookkeeping does not manufacture Axis 5 enrichment
evidence.  The extended profile inherits the base construction level exactly. -/
theorem extendProfile_preserves_enrichmentConstructionLevel
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile) :
    (extendProfile baseProfile extension).enrichmentConstructionLevel =
      baseProfile.enrichmentConstructionLevel := rfl

/-- The current extension bookkeeping only adds one finite tower node.  It
does not manufacture Axis 8 profile-category, fibration, localization, or
omega-tower evidence. -/
theorem extendProfile_preserves_fibrationConstructionLevel
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile) :
    (extendProfile baseProfile extension).fibrationConstructionLevel =
      baseProfile.fibrationConstructionLevel := rfl

/-- The current extension bookkeeping does not manufacture Axis 7 concrete
modality, adjunction, or commuting-cohesion evidence. -/
theorem extendProfile_preserves_modalConstructionLevel
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile) :
    (extendProfile baseProfile extension).modalConstructionLevel =
      baseProfile.modalConstructionLevel := rfl

/-- The current extension bookkeeping does not manufacture Axis 12 STC
logical-relation, canonicity, or normalization evidence. -/
theorem extendProfile_preserves_stcConstructionLevel
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile) :
    (extendProfile baseProfile extension).stcConstructionLevel =
      baseProfile.stcConstructionLevel := rfl

/-- The current extension bookkeeping does not manufacture Axis 13 MTT
syntax, Gratzer normalization, or conversion-decidability evidence. -/
theorem extendProfile_preserves_mttNormConstructionLevel
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile) :
    (extendProfile baseProfile extension).mttNormConstructionLevel =
      baseProfile.mttNormConstructionLevel := rfl

/-- A ProfileLens is the future conservative-extension roundtrip object.
No instance is constructed for the current eta demonstration in this file. -/
structure ProfileLens (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile) where
  /-- Lift: embed base cells into extended profile. -/
  liftDim0 : PolyTerm baseProfile 0 → PolyTerm (extendProfile baseProfile extension) 0
  /-- Forget: project extended cells back to base. -/
  forgetDim0 : PolyTerm (extendProfile baseProfile extension) 0 → PolyTerm baseProfile 0
  /-- Roundtrip: forget ∘ lift = id. -/
  roundtrip : ∀ (cell : PolyTerm baseProfile 0),
    forgetDim0 (liftDim0 cell) = cell

/-- Proof-relevant view of the five local admission evidence fields.

This is deliberately only the local admission ledger. It is not the
eventual PolyCell admissibility theorem promised by the long-range plan. -/
structure ProfileExtension.Admitted {baseProfile : PolyProfile}
    (extension : ProfileExtension baseProfile) where
  implementationEvidence : ImplementationSoundEvidence extension.interface
  bilaxCompatibilityEvidence : BilaxCompatibilityEvidence extension.interface
  conservativityEvidence : ConservativityEvidence extension.interface
  metatheoryPreservationEvidence : MetatheoryPreservationEvidence extension.interface
  erasurePreservationEvidence : ErasurePreservationEvidence extension.interface

/-- A profile extension has a local admission record when its five local
proof-relevant fields can be constructed. -/
def ProfileExtension.isAdmitted {baseProfile : PolyProfile}
    (extension : ProfileExtension baseProfile) : Prop :=
  Nonempty extension.Admitted

/-- Convert the extension fields into proof-relevant admission evidence. -/
theorem ProfileExtension.admitted_from_fields
    {baseProfile : PolyProfile}
    (extension : ProfileExtension baseProfile) :
    extension.Admitted := by
  exact {
    implementationEvidence := extension.implementationEvidence
    bilaxCompatibilityEvidence := extension.bilaxCompatibilityEvidence
    conservativityEvidence := extension.conservativityEvidence
    metatheoryPreservationEvidence := extension.metatheoryPreservationEvidence
    erasurePreservationEvidence := extension.erasurePreservationEvidence
  }

/-- The extension fields also give the Prop-level local-admission predicate. -/
theorem ProfileExtension.isAdmitted_from_fields
    {baseProfile : PolyProfile}
    (extension : ProfileExtension baseProfile) :
    extension.isAdmitted := by
  exact ⟨extension.admitted_from_fields⟩

/-- Present mechanized slice of extension preservation.

The later theorem must eventually target an `AdmissibleProfile` structure.
For now this theorem only checks the facts the implementation currently
computes: the profile tower is extended and the admission flags have
proof-relevant evidence. -/
theorem extendProfile_preserves_admission_evidence
    (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile)
    (admitted : extension.Admitted) :
    (extendProfile baseProfile extension).fibrationTower =
      .extend baseProfile.fibrationTower ∧
    extension.isAdmitted := by
  exact ⟨rfl, ⟨admitted⟩⟩

/-- Capabilities of the extended profile = meet of base and extension. -/
def extendedCapabilities (baseProfile : PolyProfile)
    (extension : ProfileExtension baseProfile)
    (baseCapabilities : MetatheoreticCapabilities) :
    MetatheoreticCapabilities :=
  baseCapabilities.meet extension.capabilities

/-- Polynomial interface for the eta-reduction demonstration extension. -/
def etaReductionInterface : PolynomialInterface where
    generatorCount := 0  -- no new term constructors
    arities := Fin.elim0
    reductionCount := 2  -- etaLam + etaPath
    reductionArities := fun _ => 1

/-- Eta-lambda's concrete reduction-rule index in the demonstration interface. -/
def etaReductionInterfaceLamIndex : Fin etaReductionInterface.reductionCount :=
  etaLamReductionIndex (interface := etaReductionInterface) rfl

/-- Eta-path's concrete reduction-rule index in the demonstration interface. -/
def etaReductionInterfacePathIndex : Fin etaReductionInterface.reductionCount :=
  etaPathReductionIndex (interface := etaReductionInterface) rfl

theorem etaReductionInterfaceLamArity_eq_one :
    etaReductionInterface.reductionArities
      etaReductionInterfaceLamIndex = 1 := rfl

theorem etaReductionInterfacePathArity_eq_one :
    etaReductionInterface.reductionArities
      etaReductionInterfacePathIndex = 1 := rfl

/-- Concrete rule-index map for the eta demonstration interface. -/
def etaReductionInterfaceRuleIndex (rule : EtaReductionRule) :
    Fin etaReductionInterface.reductionCount :=
  EtaReductionRule.indexFor (interface := etaReductionInterface) rfl rule

theorem etaReductionInterfaceRuleIndex_etaLam :
    etaReductionInterfaceRuleIndex .etaLam =
      etaReductionInterfaceLamIndex := rfl

theorem etaReductionInterfaceRuleIndex_etaPath :
    etaReductionInterfaceRuleIndex .etaPath =
      etaReductionInterfacePathIndex := rfl

theorem etaReductionInterfaceRuleArity_eq_declared
    (rule : EtaReductionRule) :
    etaReductionInterface.reductionArities
      (etaReductionInterfaceRuleIndex rule) = rule.arity := by
  cases rule <;> rfl

/-- Eta-reduction interface evidence. -/
def etaReductionInterfaceEvidence :
    EtaReductionInterfaceEvidence etaReductionInterface where
  generatorCount_eq_zero := rfl
  reductionCount_eq_two := rfl
  etaLamArity_eq_one := rfl
  etaPathArity_eq_one := rfl
  ruleArity_eq_declared := etaReductionInterfaceRuleArity_eq_declared

/-- A demonstration extension record for eta-reduction bookkeeping. -/
def etaReductionExtension : ProfileExtension fxProfile where
  interface := etaReductionInterface
  implementationEvidence := {
    etaReductionShape := etaReductionInterfaceEvidence
  }
  bilaxCompatibilityEvidence := {
    hasNoNewGenerators := etaReductionInterfaceEvidence.generatorCount_eq_zero
  }
  conservativityEvidence := {
    hasNoNewDim0Constructors := etaReductionInterfaceEvidence.generatorCount_eq_zero
  }
  metatheoryPreservationEvidence := {
    etaReductionShape := etaReductionInterfaceEvidence
  }
  erasurePreservationEvidence := {
    hasNoRuntimeConstructors := etaReductionInterfaceEvidence.generatorCount_eq_zero
  }
  fireTriangleRestriction := none
  capabilities := MetatheoreticCapabilities.top

/-- Eta extension local admission record. -/
theorem etaReductionExtension_localAdmissionRecord :
    etaReductionExtension.Admitted :=
  etaReductionExtension.admitted_from_fields

/-- Compatibility alias for the eta extension local admission record. -/
theorem etaReductionExtension_admitted :
    etaReductionExtension.Admitted :=
  etaReductionExtension_localAdmissionRecord

/-- Extended FX with eta bookkeeping as a `PolyProfile` value.  The extension
does not add an algebra-extension theorem. -/
def fxWithEta : PolyProfile :=
  extendProfile fxProfile etaReductionExtension

end LeanFX2.Foundation.PolyCell.Extension
