import FX1Poly.Modal.PrecisionOverflowCollision
import FX1Poly.Modal.MutationChainLatticeDimension

namespace FX1Poly.Modal

-- Bool helpers for the implication "demand ⟹ invariant-preserved".
theorem notImplies_iff (firstFlag secondFlag : Bool) :
    ¬ (firstFlag = true → secondFlag = true) ↔ (firstFlag = true ∧ secondFlag = false) := by
  cases firstFlag <;> cases secondFlag
  · exact ⟨fun notImpl => absurd (fun h => Bool.noConfusion h) notImpl, fun ⟨hf, _⟩ => Bool.noConfusion hf⟩
  · exact ⟨fun notImpl => absurd (fun h => Bool.noConfusion h) notImpl, fun ⟨hf, _⟩ => Bool.noConfusion hf⟩
  · exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ impl => Bool.noConfusion (impl rfl)⟩
  · exact ⟨fun notImpl => absurd (fun _ => rfl) notImpl, fun ⟨_, hf⟩ => Bool.noConfusion hf⟩

theorem implies_iff (firstFlag secondFlag : Bool) :
    (firstFlag = true → secondFlag = true) ↔ (firstFlag = false ∨ secondFlag = true) := by
  cases firstFlag <;> cases secondFlag
  · exact ⟨fun _ => Or.inl rfl, fun _ h => Bool.noConfusion h⟩
  · exact ⟨fun _ => Or.inl rfl, fun _ _ => rfl⟩
  · exact ⟨fun impl => Or.inr (impl rfl), fun disjunct _ =>
      disjunct.elim (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h)⟩
  · exact ⟨fun _ => Or.inr rfl, fun _ _ => rfl⟩

-- The generic FORM of a §6.8 cross-dimension collision.
structure SoundnessCollisionSchema where
  Demand : Type
  Capability : Type
  isStrongDemand : Demand → Bool
  preservesInvariant : Capability → Bool

def SoundnessCollisionSchema.IsConsistent (schema : SoundnessCollisionSchema)
    (demand : schema.Demand) (capability : schema.Capability) : Prop :=
  schema.isStrongDemand demand = true → schema.preservesInvariant capability = true

theorem SoundnessCollisionSchema.notConsistent_iff (schema : SoundnessCollisionSchema)
    (demand : schema.Demand) (capability : schema.Capability) :
    ¬ schema.IsConsistent demand capability ↔
      (schema.isStrongDemand demand = true ∧ schema.preservesInvariant capability = false) :=
  notImplies_iff (schema.isStrongDemand demand) (schema.preservesInvariant capability)

theorem SoundnessCollisionSchema.consistent_iff (schema : SoundnessCollisionSchema)
    (demand : schema.Demand) (capability : schema.Capability) :
    schema.IsConsistent demand capability ↔
      (schema.isStrongDemand demand = false ∨ schema.preservesInvariant capability = true) :=
  implies_iff (schema.isStrongDemand demand) (schema.preservesInvariant capability)

-- INSTANCE 1: the shipped decimal × overflow(wrap) collision (#1021), recovered through the schema.
def PrecisionGrade.isExact : PrecisionGrade → Bool
  | .exactPrecision => true
  | .inexactPrecision => false

def decimalOverflowSchema : SoundnessCollisionSchema where
  Demand := PrecisionGrade
  Capability := OverflowGrade
  isStrongDemand := PrecisionGrade.isExact
  preservesInvariant := OverflowGrade.isExactnessPreserving

theorem decimalOverflowSchema_recovers_collision :
    ¬ decimalOverflowSchema.IsConsistent PrecisionGrade.exactPrecision OverflowGrade.wrapGrade :=
  (decimalOverflowSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

-- bridge: the schema's consistency IS the shipped IsJointlyConsistent (#1021).
theorem isExact_eq_true_iff (precision : PrecisionGrade) :
    precision.isExact = true ↔ precision = PrecisionGrade.exactPrecision := by
  cases precision
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun h => Bool.noConfusion h, fun h => PrecisionGrade.noConfusion h⟩

theorem decimalOverflowSchema_consistent_iff_jointlyConsistent
    (precision : PrecisionGrade) (overflow : OverflowGrade) :
    decimalOverflowSchema.IsConsistent precision overflow ↔ IsJointlyConsistent precision overflow := by
  unfold SoundnessCollisionSchema.IsConsistent IsJointlyConsistent decimalOverflowSchema
  constructor
  · intro schemaConsistent exactEq
    exact schemaConsistent ((isExact_eq_true_iff precision).mpr exactEq)
  · intro jointConsistent exactFlag
    exact jointConsistent ((isExact_eq_true_iff precision).mp exactFlag)

-- INSTANCE 2: the NEW monotonic × concurrent collision (§6.8), over the shipped MutationGrade chain.
inductive ConcurrencyGrade where
  | sequential
  | concurrent
  deriving DecidableEq

def ConcurrencyGrade.isConcurrent : ConcurrencyGrade → Bool
  | .concurrent => true
  | .sequential => false

-- Only `immutable` (read-only) is sound under UNSYNCHRONIZED concurrent access; appendOnly/monotonic/readWrite
-- all require update sequencing (out-of-order commits break their invariant).
def MutationGrade.isConcurrencySafe : MutationGrade → Bool
  | .immutable => true
  | .appendOnly => false
  | .monotonic => false
  | .readWrite => false

def monotonicConcurrentSchema : SoundnessCollisionSchema where
  Demand := ConcurrencyGrade
  Capability := MutationGrade
  isStrongDemand := ConcurrencyGrade.isConcurrent
  preservesInvariant := MutationGrade.isConcurrencySafe

theorem concurrentCollidesWithMonotonic :
    ¬ monotonicConcurrentSchema.IsConsistent ConcurrencyGrade.concurrent MutationGrade.monotonic :=
  (monotonicConcurrentSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

theorem concurrentCollidesWithAppendOnly :
    ¬ monotonicConcurrentSchema.IsConsistent ConcurrencyGrade.concurrent MutationGrade.appendOnly :=
  (monotonicConcurrentSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

theorem concurrentCollidesWithReadWrite :
    ¬ monotonicConcurrentSchema.IsConsistent ConcurrencyGrade.concurrent MutationGrade.readWrite :=
  (monotonicConcurrentSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

theorem concurrentConsistentWithImmutable :
    monotonicConcurrentSchema.IsConsistent ConcurrencyGrade.concurrent MutationGrade.immutable :=
  fun _ => rfl

theorem sequentialConsistentWithEveryMutation (mutation : MutationGrade) :
    monotonicConcurrentSchema.IsConsistent ConcurrencyGrade.sequential mutation :=
  fun absurdFlag => Bool.noConfusion absurdFlag

end FX1Poly.Modal

#print axioms FX1Poly.Modal.SoundnessCollisionSchema.notConsistent_iff
#print axioms FX1Poly.Modal.decimalOverflowSchema_consistent_iff_jointlyConsistent
#print axioms FX1Poly.Modal.concurrentCollidesWithMonotonic
#print axioms FX1Poly.Modal.sequentialConsistentWithEveryMutation
