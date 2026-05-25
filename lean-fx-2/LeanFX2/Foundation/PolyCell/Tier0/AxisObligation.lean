/-!
# Tier 0: Axis Obligation Type

Every PolyCell axis is a Tier-0 obligation: a categorical extension
to the base type theory together with structural witnesses that
deliver metatheory (canonicity, normalization, parametricity).

Reference: polycell.md §3.0.4
-/

namespace LeanFX2.Foundation.PolyCell.Tier0

inductive FireTriangleLeg : Type where
  | substitution
  | dependentElimination
  | effects
  deriving DecidableEq, Repr

/-- Finite status for a metatheoretic capability in the current ledger.

This is intentionally not proof of the theorem named by the field. It is the
computable capability bound used by profile-extension bookkeeping. -/
inductive CapabilityStatus where
  | available
  | unavailable
  deriving DecidableEq, Repr

def CapabilityStatus.rank : CapabilityStatus → Nat
  | .available => 1
  | .unavailable => 0

def CapabilityStatus.ofRank : Nat → CapabilityStatus
  | 1 => .available
  | _ => .unavailable

def CapabilityStatus.meet (statusA statusB : CapabilityStatus) :
    CapabilityStatus :=
  CapabilityStatus.ofRank (Nat.min statusA.rank statusB.rank)

theorem CapabilityStatus.meet_comm
    (statusA statusB : CapabilityStatus) :
    statusA.meet statusB = statusB.meet statusA := by
  cases statusA <;> cases statusB <;> rfl

theorem CapabilityStatus.meet_idempotent
    (status : CapabilityStatus) :
    status.meet status = status := by
  cases status <;> rfl

structure MetatheoreticCapabilities where
  canonicityStatus : CapabilityStatus
  normalizationStatus : CapabilityStatus
  parametricityStatus : CapabilityStatus
  subjectReductionStatus : CapabilityStatus
  confluenceStatus : CapabilityStatus
  strongNormalizationStatus : CapabilityStatus
  decidableConversionStatus : CapabilityStatus
  decidableTypecheckingStatus : CapabilityStatus
  deriving DecidableEq, Repr

def MetatheoreticCapabilities.meet
    (capA capB : MetatheoreticCapabilities) :
    MetatheoreticCapabilities where
  canonicityStatus := capA.canonicityStatus.meet capB.canonicityStatus
  normalizationStatus := capA.normalizationStatus.meet capB.normalizationStatus
  parametricityStatus := capA.parametricityStatus.meet capB.parametricityStatus
  subjectReductionStatus := capA.subjectReductionStatus.meet capB.subjectReductionStatus
  confluenceStatus := capA.confluenceStatus.meet capB.confluenceStatus
  strongNormalizationStatus := capA.strongNormalizationStatus.meet capB.strongNormalizationStatus
  decidableConversionStatus := capA.decidableConversionStatus.meet capB.decidableConversionStatus
  decidableTypecheckingStatus := capA.decidableTypecheckingStatus.meet capB.decidableTypecheckingStatus

instance : Min MetatheoreticCapabilities where
  min := MetatheoreticCapabilities.meet

def MetatheoreticCapabilities.top : MetatheoreticCapabilities where
  canonicityStatus := .available
  normalizationStatus := .available
  parametricityStatus := .available
  subjectReductionStatus := .available
  confluenceStatus := .available
  strongNormalizationStatus := .available
  decidableConversionStatus := .available
  decidableTypecheckingStatus := .available

def MetatheoreticCapabilities.bot : MetatheoreticCapabilities where
  canonicityStatus := .unavailable
  normalizationStatus := .unavailable
  parametricityStatus := .unavailable
  subjectReductionStatus := .unavailable
  confluenceStatus := .unavailable
  strongNormalizationStatus := .unavailable
  decidableConversionStatus := .unavailable
  decidableTypecheckingStatus := .unavailable

theorem MetatheoreticCapabilities.meet_comm (capA capB : MetatheoreticCapabilities) :
    capA.meet capB = capB.meet capA := by
  cases capA; cases capB; unfold meet; congr 1 <;> apply CapabilityStatus.meet_comm

theorem MetatheoreticCapabilities.meet_idempotent (cap : MetatheoreticCapabilities) :
    cap.meet cap = cap := by
  cases cap; unfold meet; congr 1 <;> apply CapabilityStatus.meet_idempotent

inductive ConsistencyStrength : Type where
  | leanCore
  | zfc
  | zfcInaccessible
  | zfcMahlo
  | zfcLargeCardinal
  deriving DecidableEq, Repr, Ord

inductive AxisId : Type where
  | shape
  | algebra
  | stratification
  | saturation
  | enrichment
  | complicialGray
  | multiModal
  | profileFibration
  | omegacE
  | universe
  | singleSubstitution
  | syntheticTait
  | mttNormalization
  deriving DecidableEq, Repr

structure Citation where
  authors : String
  title : String
  arxivId : Option String
  year : Nat
  deriving DecidableEq, Repr

structure AxisObligation where
  axisName : String
  axisId : AxisId
  fireTriangleRestriction : Option FireTriangleLeg
  capabilities : MetatheoreticCapabilities
  estimatedLinesOfCode : Nat
  precedents : List Citation
  deriving Repr

end LeanFX2.Foundation.PolyCell.Tier0
