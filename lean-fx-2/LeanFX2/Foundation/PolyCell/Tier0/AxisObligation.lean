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

structure MetatheoreticCapabilities where
  preservesCanonicity : Bool
  preservesNormalization : Bool
  preservesParametricity : Bool
  preservesSubjectReduction : Bool
  preservesConfluence : Bool
  preservesStrongNormalization : Bool
  preservesDecidableConversion : Bool
  preservesDecidableTypechecking : Bool
  deriving DecidableEq, Repr

def MetatheoreticCapabilities.meet
    (capA capB : MetatheoreticCapabilities) :
    MetatheoreticCapabilities where
  preservesCanonicity := capA.preservesCanonicity && capB.preservesCanonicity
  preservesNormalization := capA.preservesNormalization && capB.preservesNormalization
  preservesParametricity := capA.preservesParametricity && capB.preservesParametricity
  preservesSubjectReduction := capA.preservesSubjectReduction && capB.preservesSubjectReduction
  preservesConfluence := capA.preservesConfluence && capB.preservesConfluence
  preservesStrongNormalization := capA.preservesStrongNormalization && capB.preservesStrongNormalization
  preservesDecidableConversion := capA.preservesDecidableConversion && capB.preservesDecidableConversion
  preservesDecidableTypechecking := capA.preservesDecidableTypechecking && capB.preservesDecidableTypechecking

instance : Min MetatheoreticCapabilities where
  min := MetatheoreticCapabilities.meet

def MetatheoreticCapabilities.top : MetatheoreticCapabilities where
  preservesCanonicity := true
  preservesNormalization := true
  preservesParametricity := true
  preservesSubjectReduction := true
  preservesConfluence := true
  preservesStrongNormalization := true
  preservesDecidableConversion := true
  preservesDecidableTypechecking := true

def MetatheoreticCapabilities.bot : MetatheoreticCapabilities where
  preservesCanonicity := false
  preservesNormalization := false
  preservesParametricity := false
  preservesSubjectReduction := false
  preservesConfluence := false
  preservesStrongNormalization := false
  preservesDecidableConversion := false
  preservesDecidableTypechecking := false

theorem MetatheoreticCapabilities.meet_comm (capA capB : MetatheoreticCapabilities) :
    capA.meet capB = capB.meet capA := by
  cases capA; cases capB; unfold meet; congr 1 <;> apply Bool.and_comm

theorem MetatheoreticCapabilities.meet_idempotent (cap : MetatheoreticCapabilities) :
    cap.meet cap = cap := by
  cases cap; unfold meet; congr 1 <;> apply Bool.and_self

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
