import FX1Poly.Modal.SoundnessCollisionSchema

namespace FX1Poly.Modal

-- Part 1: ghost × runtime — a CO-OCCURRENCE collision (unsound on mere joint presence).

inductive ObservationDemand where
  | runtimeObserved
  | ghostOnly
  deriving DecidableEq

def ObservationDemand.isRuntimeObserved : ObservationDemand → Bool
  | .runtimeObserved => true
  | .ghostOnly => false

inductive ErasureCapability where
  | erasedGhost
  | runtimePresent
  deriving DecidableEq

def ErasureCapability.isObservabilityPreserving : ErasureCapability → Bool
  | .runtimePresent => true
  | .erasedGhost => false

def ghostRuntimeSchema : SoundnessCollisionSchema where
  Demand := ObservationDemand
  Capability := ErasureCapability
  isStrongDemand := ObservationDemand.isRuntimeObserved
  preservesInvariant := ErasureCapability.isObservabilityPreserving

theorem ghostObservedAtRuntimeCollision :
    ¬ ghostRuntimeSchema.IsConsistent ObservationDemand.runtimeObserved ErasureCapability.erasedGhost :=
  (ghostRuntimeSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

theorem runtimePresentValueObservable :
    ghostRuntimeSchema.IsConsistent ObservationDemand.runtimeObserved ErasureCapability.runtimePresent :=
  fun _ => rfl

theorem unobservedGhostConsistent (erasure : ErasureCapability) :
    ghostRuntimeSchema.IsConsistent ObservationDemand.ghostOnly erasure :=
  fun absurdFlag => Bool.noConfusion absurdFlag

-- Part 2: borrow × Async — a SCOPING-REFINED collision (demand = the ESCAPE control, not presence).

inductive BorrowEscapeDemand where
  | escapesScope
  | confinedToScope
  deriving DecidableEq

def BorrowEscapeDemand.isEscaping : BorrowEscapeDemand → Bool
  | .escapesScope => true
  | .confinedToScope => false

inductive AsyncContext where
  | asyncGranted
  | asyncAbsent
  deriving DecidableEq

def AsyncContext.isBorrowConfining : AsyncContext → Bool
  | .asyncAbsent => true
  | .asyncGranted => false

def borrowAsyncSchema : SoundnessCollisionSchema where
  Demand := BorrowEscapeDemand
  Capability := AsyncContext
  isStrongDemand := BorrowEscapeDemand.isEscaping
  preservesInvariant := AsyncContext.isBorrowConfining

theorem borrowEscapeUnderAsyncCollision :
    ¬ borrowAsyncSchema.IsConsistent BorrowEscapeDemand.escapesScope AsyncContext.asyncGranted :=
  (borrowAsyncSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

theorem confinedBorrowUnderAsyncConsistent :
    borrowAsyncSchema.IsConsistent BorrowEscapeDemand.confinedToScope AsyncContext.asyncGranted :=
  fun absurdFlag => Bool.noConfusion absurdFlag

-- Part 3: borrow × unscoped spawn — the scoping-refined twin (task_group confines).

inductive SpawnContext where
  | unscopedSpawn
  | scopedSpawn
  deriving DecidableEq

def SpawnContext.isBorrowConfining : SpawnContext → Bool
  | .scopedSpawn => true
  | .unscopedSpawn => false

def borrowSpawnSchema : SoundnessCollisionSchema where
  Demand := BorrowEscapeDemand
  Capability := SpawnContext
  isStrongDemand := BorrowEscapeDemand.isEscaping
  preservesInvariant := SpawnContext.isBorrowConfining

theorem borrowEscapeIntoUnscopedSpawnCollision :
    ¬ borrowSpawnSchema.IsConsistent BorrowEscapeDemand.escapesScope SpawnContext.unscopedSpawn :=
  (borrowSpawnSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

theorem borrowIntoScopedSpawnConsistent :
    borrowSpawnSchema.IsConsistent BorrowEscapeDemand.escapesScope SpawnContext.scopedSpawn :=
  fun _ => rfl

-- Part 4: the structural dichotomy of the §6.8 catalog.

theorem catalogHasTwoCollisionClasses :
    (¬ ghostRuntimeSchema.IsConsistent ObservationDemand.runtimeObserved ErasureCapability.erasedGhost) ∧
    borrowAsyncSchema.IsConsistent BorrowEscapeDemand.confinedToScope AsyncContext.asyncGranted :=
  ⟨ghostObservedAtRuntimeCollision, confinedBorrowUnderAsyncConsistent⟩

end FX1Poly.Modal

#print axioms FX1Poly.Modal.ghostObservedAtRuntimeCollision
#print axioms FX1Poly.Modal.unobservedGhostConsistent
#print axioms FX1Poly.Modal.borrowEscapeUnderAsyncCollision
#print axioms FX1Poly.Modal.confinedBorrowUnderAsyncConsistent
#print axioms FX1Poly.Modal.borrowEscapeIntoUnscopedSpawnCollision
#print axioms FX1Poly.Modal.borrowIntoScopedSpawnConsistent
#print axioms FX1Poly.Modal.catalogHasTwoCollisionClasses
