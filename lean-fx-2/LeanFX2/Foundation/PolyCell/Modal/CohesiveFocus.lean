/-!
# Cohesive Focuses — Axis 7 Finite Doctrine Ledger

Only 4 of FX's 21 dimensions are true cohesive focuses in the
Myers-Riley sense (each with its own ♭ ⊣ ◇ ⊣ □ ⊣ ♯ adjoint chain):
differential, equivariant, simplicial, real.

The other 17 dimensions are grades/effects/security/refinements handled
by separate doctrines (resource semiring, cost algebra, DCC, etc.).

This file currently records the finite focus set, operation-record
interfaces, and a finite detector relation used by the scaffold.  It does
not construct Myers-Riley adjunction instances, commuting-modality
theorems, or a Myers-Riley doctrine package.

Reference: arXiv:2301.13780 §2-6.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Modal

universe u

/-- Construction ledger for Axis 7 modal/cohesive machinery.

The levels separate finite bookkeeping from genuine modality instances and
commuting-cohesion theorems. -/
inductive ModalConstructionLevel where
  /-- Only the four FX focus names are present. -/
  | focusEnumeration
  /-- Operation-record interfaces for modality symbols are present. -/
  | operationRecordInterfaces
  /-- A finite detector relation has been enumerated. -/
  | finiteDetectorRelation
  /-- Finite detector-pair orthogonality witnesses have been recorded. -/
  | finiteOrthogonalityWitnesses
  /-- Concrete modality operation values have been supplied. -/
  | modalityInstances
  /-- Concrete adjunction witnesses have been supplied. -/
  | adjunctionWitnessInstances
  /-- Commuting-cohesion theorem interfaces are available from adjunction data. -/
  | commutingCohesionTheorems
  /-- A Myers-Riley doctrine package has been mechanized. -/
  | myersRileyDoctrine
  deriving DecidableEq, Repr

def ModalConstructionLevel.hasFocusEnumeration :
    ModalConstructionLevel → Bool
  | .focusEnumeration => true
  | .operationRecordInterfaces => true
  | .finiteDetectorRelation => true
  | .finiteOrthogonalityWitnesses => true
  | .modalityInstances => true
  | .adjunctionWitnessInstances => true
  | .commutingCohesionTheorems => true
  | .myersRileyDoctrine => true

def ModalConstructionLevel.hasOperationRecordInterfaces :
    ModalConstructionLevel → Bool
  | .focusEnumeration => false
  | .operationRecordInterfaces => true
  | .finiteDetectorRelation => true
  | .finiteOrthogonalityWitnesses => true
  | .modalityInstances => true
  | .adjunctionWitnessInstances => true
  | .commutingCohesionTheorems => true
  | .myersRileyDoctrine => true

def ModalConstructionLevel.hasFiniteDetectorRelation :
    ModalConstructionLevel → Bool
  | .focusEnumeration => false
  | .operationRecordInterfaces => false
  | .finiteDetectorRelation => true
  | .finiteOrthogonalityWitnesses => true
  | .modalityInstances => true
  | .adjunctionWitnessInstances => true
  | .commutingCohesionTheorems => true
  | .myersRileyDoctrine => true

def ModalConstructionLevel.hasFiniteOrthogonalityWitnesses :
    ModalConstructionLevel → Bool
  | .focusEnumeration => false
  | .operationRecordInterfaces => false
  | .finiteDetectorRelation => false
  | .finiteOrthogonalityWitnesses => true
  | .modalityInstances => true
  | .adjunctionWitnessInstances => true
  | .commutingCohesionTheorems => true
  | .myersRileyDoctrine => true

def ModalConstructionLevel.hasModalityInstances :
    ModalConstructionLevel → Bool
  | .focusEnumeration => false
  | .operationRecordInterfaces => false
  | .finiteDetectorRelation => false
  | .finiteOrthogonalityWitnesses => false
  | .modalityInstances => true
  | .adjunctionWitnessInstances => true
  | .commutingCohesionTheorems => true
  | .myersRileyDoctrine => true

def ModalConstructionLevel.hasAdjunctionWitnessInstances :
    ModalConstructionLevel → Bool
  | .focusEnumeration => false
  | .operationRecordInterfaces => false
  | .finiteDetectorRelation => false
  | .finiteOrthogonalityWitnesses => false
  | .modalityInstances => false
  | .adjunctionWitnessInstances => true
  | .commutingCohesionTheorems => true
  | .myersRileyDoctrine => true

def ModalConstructionLevel.hasCommutingCohesionTheorems :
    ModalConstructionLevel → Bool
  | .focusEnumeration => false
  | .operationRecordInterfaces => false
  | .finiteDetectorRelation => false
  | .finiteOrthogonalityWitnesses => false
  | .modalityInstances => false
  | .adjunctionWitnessInstances => false
  | .commutingCohesionTheorems => true
  | .myersRileyDoctrine => true

def ModalConstructionLevel.hasMyersRileyDoctrine :
    ModalConstructionLevel → Bool
  | .focusEnumeration => false
  | .operationRecordInterfaces => false
  | .finiteDetectorRelation => false
  | .finiteOrthogonalityWitnesses => false
  | .modalityInstances => false
  | .adjunctionWitnessInstances => false
  | .commutingCohesionTheorems => false
  | .myersRileyDoctrine => true

/-- Present status: finite focus names, operation-record interfaces, detector
relation entries, and detector-pair witnesses.  No concrete modality,
adjunction, or commuting-cohesion theorem is claimed. -/
def fxModalConstructionLevel : ModalConstructionLevel :=
  .finiteOrthogonalityWitnesses

/-- The 4 true cohesive focuses in FX. -/
inductive CohesiveFocus where
  | differential
  | equivariant
  | simplicial
  | real
  deriving DecidableEq, Repr

/-- The finite list of FX focuses used by the scaffold. -/
def fxCohesiveFocuses : List CohesiveFocus :=
  [.differential, .equivariant, .simplicial, .real]

/-- Number of FX cohesive focuses recorded in the finite list. -/
def fxCohesiveFocusCount : Nat :=
  fxCohesiveFocuses.length

/-- The scaffold focus list contains four entries. -/
theorem fxCohesiveFocuses_length :
    fxCohesiveFocusCount = 4 := rfl

/-- A cohesive modality operation record.

Each field is only a type-level operation name.  This record does not assert
endofunctor laws, adjunctions, or commutation laws. -/
structure CohesiveModality (focus : CohesiveFocus) where
  /-- Shape (∫): extracts the "underlying discrete shape" of a type. -/
  shapeOp : Type u → Type u
  /-- Flat (♭): makes a type "discrete" (forgets cohesive structure). -/
  flatOp : Type u → Type u
  /-- Diamond (◇): a placeholder for the middle left modality. -/
  diamondOp : Type u → Type u
  /-- Box (□): a placeholder for the middle right modality. -/
  boxOp : Type u → Type u
  /-- Sharp (♯): a placeholder for the codiscrete modality. -/
  sharpOp : Type u → Type u

/-- A direct witness record for one adjunction between type-level operations.

The triangular laws are not part of this scaffold record. -/
structure AdjunctionWitness (leftFunctor rightFunctor : Type u → Type u) where
  /-- Unit: A → right(left(A)). -/
  unit : (carrier : Type u) → carrier → rightFunctor (leftFunctor carrier)
  /-- Counit: left(right(A)) → A. -/
  counit : (carrier : Type u) → leftFunctor (rightFunctor carrier) → carrier

/-- A cohesive adjunction-interface structure: operation record plus
adjunction-witness records.  This is still not a commuting-cohesion theorem. -/
structure CohesiveAdjunctionStructure (focus : CohesiveFocus) extends
    CohesiveModality focus where
  /-- ∫ ⊣ ♭: shape is left adjoint to flat. -/
  shapeFlatAdj : AdjunctionWitness shapeOp flatOp
  /-- ♭ ⊣ ◇: flat is left adjoint to diamond. -/
  flatDiamondAdj : AdjunctionWitness flatOp diamondOp
  /-- ◇ ⊣ □: diamond is left adjoint to box. -/
  diamondBoxAdj : AdjunctionWitness diamondOp boxOp
  /-- □ ⊣ ♯: box is left adjoint to sharp. -/
  boxSharpAdj : AdjunctionWitness boxOp sharpOp

/-- Finite detector-pair relation used by the current scaffold.

These constructors are bookkeeping entries, not proofs derived from concrete
modality data. -/
inductive DetectorDiscrete : CohesiveFocus → CohesiveFocus → Prop where
  | differentialSelf : DetectorDiscrete .differential .differential
  | equivariantSelf : DetectorDiscrete .equivariant .equivariant
  | simplicialSelf : DetectorDiscrete .simplicial .simplicial
  | realSelf : DetectorDiscrete .real .real
  | equivariantDifferential : DetectorDiscrete .equivariant .differential
  | differentialEquivariant : DetectorDiscrete .differential .equivariant
  | simplicialEquivariant : DetectorDiscrete .simplicial .equivariant
  | equivariantSimplicial : DetectorDiscrete .equivariant .simplicial

/-- Computable readback for the finite detector-pair relation. -/
def DetectorDiscrete.isDetected
    (focusSource focusTarget : CohesiveFocus) : Bool :=
  match focusSource with
  | .differential =>
      match focusTarget with
      | .differential => true
      | .equivariant => true
      | .simplicial => false
      | .real => false
  | .equivariant =>
      match focusTarget with
      | .differential => true
      | .equivariant => true
      | .simplicial => true
      | .real => false
  | .simplicial =>
      match focusTarget with
      | .differential => false
      | .equivariant => true
      | .simplicial => true
      | .real => false
  | .real =>
      match focusTarget with
      | .differential => false
      | .equivariant => false
      | .simplicial => false
      | .real => true

/-- Every inductive detector entry is accepted by the computable readback. -/
theorem DetectorDiscrete.isDetected_complete
    {focusSource focusTarget : CohesiveFocus} :
    DetectorDiscrete focusSource focusTarget →
      DetectorDiscrete.isDetected focusSource focusTarget = true
  | .differentialSelf => rfl
  | .equivariantSelf => rfl
  | .simplicialSelf => rfl
  | .realSelf => rfl
  | .equivariantDifferential => rfl
  | .differentialEquivariant => rfl
  | .simplicialEquivariant => rfl
  | .equivariantSimplicial => rfl

/-- Every positive computable detector readback is an inductive detector entry. -/
theorem DetectorDiscrete.isDetected_sound
    {focusSource focusTarget : CohesiveFocus} :
    DetectorDiscrete.isDetected focusSource focusTarget = true →
      DetectorDiscrete focusSource focusTarget := by
  cases focusSource
  · cases focusTarget
    · intro detectorEvidence
      exact DetectorDiscrete.differentialSelf
    · intro detectorEvidence
      exact DetectorDiscrete.differentialEquivariant
    · intro detectorEvidence
      cases detectorEvidence
    · intro detectorEvidence
      cases detectorEvidence
  · cases focusTarget
    · intro detectorEvidence
      exact DetectorDiscrete.equivariantDifferential
    · intro detectorEvidence
      exact DetectorDiscrete.equivariantSelf
    · intro detectorEvidence
      exact DetectorDiscrete.equivariantSimplicial
    · intro detectorEvidence
      cases detectorEvidence
  · cases focusTarget
    · intro detectorEvidence
      cases detectorEvidence
    · intro detectorEvidence
      exact DetectorDiscrete.simplicialEquivariant
    · intro detectorEvidence
      exact DetectorDiscrete.simplicialSelf
    · intro detectorEvidence
      cases detectorEvidence
  · cases focusTarget
    · intro detectorEvidence
      cases detectorEvidence
    · intro detectorEvidence
      cases detectorEvidence
    · intro detectorEvidence
      cases detectorEvidence
    · intro detectorEvidence
      exact DetectorDiscrete.realSelf

/-- Decidable detector membership derived from the finite computable readback. -/
def DetectorDiscrete.decidable
    (focusSource focusTarget : CohesiveFocus) :
    Decidable (DetectorDiscrete focusSource focusTarget) :=
  if detectorEvidence :
      DetectorDiscrete.isDetected focusSource focusTarget = true then
    isTrue (DetectorDiscrete.isDetected_sound detectorEvidence)
  else
    isFalse fun detectorEntry =>
      detectorEvidence (DetectorDiscrete.isDetected_complete detectorEntry)

instance instDecidableDetectorDiscrete
    (focusSource focusTarget : CohesiveFocus) :
    Decidable (DetectorDiscrete focusSource focusTarget) :=
  DetectorDiscrete.decidable focusSource focusTarget

/-- Detector-pair orthogonality witness.

This packages two detector entries.  It is not yet a proof that concrete
modalities commute. -/
structure CohesiveOrthogonality (focus1 focus2 : CohesiveFocus) : Prop where
  detector12 : DetectorDiscrete focus1 focus2
  detector21 : DetectorDiscrete focus2 focus1

/-- Finite detector witness for the equivariant/differential pair. -/
theorem equivariantDifferentialDetectorOrthogonality :
    CohesiveOrthogonality .equivariant .differential where
  detector12 := DetectorDiscrete.equivariantDifferential
  detector21 := DetectorDiscrete.differentialEquivariant

/-- Finite detector witness for the simplicial/equivariant pair. -/
theorem simplicialEquivariantDetectorOrthogonality :
    CohesiveOrthogonality .simplicial .equivariant where
  detector12 := DetectorDiscrete.simplicialEquivariant
  detector21 := DetectorDiscrete.equivariantSimplicial

/-- The FX cohesive doctrine interface: four modality records plus two
finite detector-pair witnesses. -/
structure FXCohesiveDoctrine where
  differentialMod : CohesiveModality .differential
  equivariantMod : CohesiveModality .equivariant
  simplicialMod : CohesiveModality .simplicial
  realMod : CohesiveModality .real
  equivDiffOrthogonal : CohesiveOrthogonality .equivariant .differential
  simplEquivOrthogonal : CohesiveOrthogonality .simplicial .equivariant

theorem fxModalConstructionLevel_eq :
    fxModalConstructionLevel =
      ModalConstructionLevel.finiteOrthogonalityWitnesses := rfl

theorem fxModal_hasFocusEnumeration :
    fxModalConstructionLevel.hasFocusEnumeration = true := rfl

theorem fxModal_hasOperationRecordInterfaces :
    fxModalConstructionLevel.hasOperationRecordInterfaces = true := rfl

theorem fxModal_hasFiniteDetectorRelation :
    fxModalConstructionLevel.hasFiniteDetectorRelation = true := rfl

theorem fxModal_hasFiniteOrthogonalityWitnesses :
    fxModalConstructionLevel.hasFiniteOrthogonalityWitnesses = true := rfl

theorem fxModal_hasNoModalityInstances :
    fxModalConstructionLevel.hasModalityInstances = false := rfl

theorem fxModal_hasNoAdjunctionWitnessInstances :
    fxModalConstructionLevel.hasAdjunctionWitnessInstances = false := rfl

theorem fxModal_hasNoCommutingCohesionTheorems :
    fxModalConstructionLevel.hasCommutingCohesionTheorems = false := rfl

theorem fxModal_hasNoMyersRileyDoctrine :
    fxModalConstructionLevel.hasMyersRileyDoctrine = false := rfl

end LeanFX2.Foundation.PolyCell.Modal
