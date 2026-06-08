import FX1Poly.Modal.PrecisionOverflowCollision
import FX1Poly.Modal.MutationChainLatticeDimension

/-! # FX1Poly/Modal/SoundnessCollisionSchema
    — the §6.8 cross-dimension collision FORM, abstracted; two collisions as instances of ONE schema

`PrecisionOverflowCollision.lean` (#1021) shipped the first mechanized §6.8 collision (`decimal ×
overflow(wrap)`).  This file makes the structural observation that the §6.8 catalog (`classified × Fail`,
`borrow × Async`, `CT × Async`, `ghost × runtime`, `monotonic × concurrent`, `decimal × overflow(wrap)`, …) is
NOT a list of unrelated bugs but instances of ONE algebraic pattern, and mechanizes that pattern:

  **A §6.8 collision is a strong GUARANTEE-demand from one dimension meeting a CAPABILITY from another dimension
  that fails to preserve the guarantee's invariant.**

`SoundnessCollisionSchema` captures exactly this: a `Demand` type with `isStrongDemand` (does this demand require
the invariant?) and a `Capability` type with `preservesInvariant` (does this capability keep it?).  Consistency
is the implication `strong demand ⟹ invariant preserved`; the collision is its negation — `strong demand AND
non-preserving capability` (`notConsistent_iff`).  Proven ONCE, generically, then instantiated:

  * **Instance 1 — `decimalOverflowSchema`** recovers the shipped #1021 collision (`decimalOverflowSchema_
    recovers_collision`), and `decimalOverflowSchema_consistent_iff_jointlyConsistent` proves the schema's
    `IsConsistent` IS #1021's `IsJointlyConsistent` — the schema genuinely subsumes the bespoke formalization.
  * **Instance 2 — `monotonicConcurrentSchema`** (NEW) over the shipped `MutationGrade` chain (§6.3 Dim 18):
    `concurrentCollidesWithMonotonic` (★) — a `monotonic` value (forward-only in a partial order) is unsound
    under UNSYNCHRONIZED concurrent access (out-of-order commits break monotonicity).  The `appendOnly` /
    `readWrite` twins collide identically (all three need update sequencing); only `immutable` (read-only) is
    sound concurrently (`concurrentConsistentWithImmutable`); and a `sequential` demand never collides
    (`sequentialConsistentWithEveryMutation`).

The payoff is the unification: two §6.8 collisions drawn from FOUR different dimensions (precision, overflow,
mutation, concurrency) are the same theorem applied twice.  Future §6.8 entries (classified × Fail, ghost ×
runtime, …) are one `SoundnessCollisionSchema` value each, with the collision/consistency facts free from the
generic characterization.

## Honest scope boundary

This models the COMBINE-time joint-consistency CONSTRAINT between two dimension grades — the algebraic face of
§6.8.  It does not wire these constraints into the term-level grade-vector checker (`GradeVector`); the schema IS
the constraint such a checker would enforce.  `ConcurrencyGrade` is a minimal 2-valued companion (the
collision-relevant projection of the §6.3 Dim 19 reentrancy / concurrency axis), mirroring how #1021's
`PrecisionGrade` is the 2-valued projection of the ULP-error precision dimension.

## Zero-axiom verification

The generic characterizations reduce to two Bool-implication lemmas (`notImplies_iff` / `implies_iff`, 4-case
`cases <;>` with `Bool.noConfusion` leaves); the instances' collisions are `(notConsistent_iff _ _).mpr ⟨rfl,
rfl⟩`; the positives are `fun _ => rfl` / `Bool.noConfusion`; the #1021 bridge threads `isExact_eq_true_iff`
(`cases` + `noConfusion`).  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- The Bool-implication negation: `¬(a ⟹ b)` iff `a` holds and `b` fails.  The truth-table heart of every
collision (`a` = strong demand, `b` = invariant preserved). -/
theorem notImplies_iff (firstFlag secondFlag : Bool) :
    ¬ (firstFlag = true → secondFlag = true) ↔ (firstFlag = true ∧ secondFlag = false) := by
  cases firstFlag <;> cases secondFlag
  · exact ⟨fun notImpl => absurd (fun h => Bool.noConfusion h) notImpl, fun ⟨hf, _⟩ => Bool.noConfusion hf⟩
  · exact ⟨fun notImpl => absurd (fun h => Bool.noConfusion h) notImpl, fun ⟨hf, _⟩ => Bool.noConfusion hf⟩
  · exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ impl => Bool.noConfusion (impl rfl)⟩
  · exact ⟨fun notImpl => absurd (fun _ => rfl) notImpl, fun ⟨_, hf⟩ => Bool.noConfusion hf⟩

/-- The positive Bool-implication law: `a ⟹ b` iff `a` is absent or `b` holds.  The consistency dual of
`notImplies_iff`. -/
theorem implies_iff (firstFlag secondFlag : Bool) :
    (firstFlag = true → secondFlag = true) ↔ (firstFlag = false ∨ secondFlag = true) := by
  cases firstFlag <;> cases secondFlag
  · exact ⟨fun _ => Or.inl rfl, fun _ h => Bool.noConfusion h⟩
  · exact ⟨fun _ => Or.inl rfl, fun _ _ => rfl⟩
  · exact ⟨fun impl => Or.inr (impl rfl), fun disjunct _ =>
      disjunct.elim (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h)⟩
  · exact ⟨fun _ => Or.inr rfl, fun _ _ => rfl⟩

/-- **The §6.8 cross-dimension soundness-collision FORM.**  A `Demand` grade from one dimension (with
`isStrongDemand`: does it require the guarantee's invariant?) and a `Capability` grade from another (with
`preservesInvariant`: does it keep it?).  Every §6.8 collision is one value of this structure. -/
structure SoundnessCollisionSchema where
  Demand : Type
  Capability : Type
  isStrongDemand : Demand → Bool
  preservesInvariant : Capability → Bool

/-- Joint consistency: a strong demand is only consistent with a capability that preserves its invariant. -/
def SoundnessCollisionSchema.IsConsistent (schema : SoundnessCollisionSchema)
    (demand : schema.Demand) (capability : schema.Capability) : Prop :=
  schema.isStrongDemand demand = true → schema.preservesInvariant capability = true

/-- **The generic collision characterization**: a (demand, capability) pair COLLIDES iff the demand is strong AND
the capability fails to preserve the invariant.  Proven once; every instance's collision is a corollary. -/
theorem SoundnessCollisionSchema.notConsistent_iff (schema : SoundnessCollisionSchema)
    (demand : schema.Demand) (capability : schema.Capability) :
    ¬ schema.IsConsistent demand capability ↔
      (schema.isStrongDemand demand = true ∧ schema.preservesInvariant capability = false) :=
  notImplies_iff (schema.isStrongDemand demand) (schema.preservesInvariant capability)

/-- **The generic consistency characterization**: a pair is consistent iff the demand is weak OR the capability
preserves the invariant. -/
theorem SoundnessCollisionSchema.consistent_iff (schema : SoundnessCollisionSchema)
    (demand : schema.Demand) (capability : schema.Capability) :
    schema.IsConsistent demand capability ↔
      (schema.isStrongDemand demand = false ∨ schema.preservesInvariant capability = true) :=
  implies_iff (schema.isStrongDemand demand) (schema.preservesInvariant capability)

/-! ## Instance 1 — `decimal × overflow(wrap)` (#1021) as a schema instance -/

/-- The strong-demand predicate for the precision dimension: exact precision is the demanding grade. -/
def PrecisionGrade.isExact : PrecisionGrade → Bool
  | .exactPrecision => true
  | .inexactPrecision => false

/-- The #1021 collision as a `SoundnessCollisionSchema`: precision demands exactness, overflow modes may or may
not preserve it (`isExactnessPreserving`). -/
def decimalOverflowSchema : SoundnessCollisionSchema where
  Demand := PrecisionGrade
  Capability := OverflowGrade
  isStrongDemand := PrecisionGrade.isExact
  preservesInvariant := OverflowGrade.isExactnessPreserving

/-- The schema RECOVERS the shipped #1021 collision: exact precision collides with wrap overflow. -/
theorem decimalOverflowSchema_recovers_collision :
    ¬ decimalOverflowSchema.IsConsistent PrecisionGrade.exactPrecision OverflowGrade.wrapGrade :=
  (decimalOverflowSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

/-- `isExact` decides exact-precision: `precision.isExact = true ↔ precision = exactPrecision`. -/
theorem isExact_eq_true_iff (precision : PrecisionGrade) :
    precision.isExact = true ↔ precision = PrecisionGrade.exactPrecision := by
  cases precision
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun h => Bool.noConfusion h, fun h => PrecisionGrade.noConfusion h⟩

/-- **The schema SUBSUMES #1021**: `decimalOverflowSchema.IsConsistent` is exactly the bespoke
`IsJointlyConsistent` (#1021).  The generic schema is not a parallel re-formalization — it recovers the shipped
collision definitionally up to the `isExact ↔ = exactPrecision` reading. -/
theorem decimalOverflowSchema_consistent_iff_jointlyConsistent
    (precision : PrecisionGrade) (overflow : OverflowGrade) :
    decimalOverflowSchema.IsConsistent precision overflow ↔ IsJointlyConsistent precision overflow := by
  unfold SoundnessCollisionSchema.IsConsistent IsJointlyConsistent decimalOverflowSchema
  constructor
  · intro schemaConsistent exactEq
    exact schemaConsistent ((isExact_eq_true_iff precision).mpr exactEq)
  · intro jointConsistent exactFlag
    exact jointConsistent ((isExact_eq_true_iff precision).mp exactFlag)

/-! ## Instance 2 — `monotonic × concurrent` (NEW) over the shipped MutationGrade chain -/

/-- The concurrency dimension (§6.3 Dim 19 reentrancy/concurrency axis), collision-relevant 2-valued projection:
`sequential` (synchronized) vs `concurrent` (unsynchronized — the demanding grade). -/
inductive ConcurrencyGrade where
  | sequential
  | concurrent
  deriving DecidableEq

/-- The strong-demand predicate: unsynchronized concurrent access is the demanding grade. -/
def ConcurrencyGrade.isConcurrent : ConcurrencyGrade → Bool
  | .concurrent => true
  | .sequential => false

/-- Is a mutation mode sound under UNSYNCHRONIZED concurrent access?  Only `immutable` (read-only) is —
`appendOnly` (tail-pointer race), `monotonic` (out-of-order commits break the forward-only invariant), and
`readWrite` (arbitrary races) all require update sequencing. -/
def MutationGrade.isConcurrencySafe : MutationGrade → Bool
  | .immutable => true
  | .appendOnly => false
  | .monotonic => false
  | .readWrite => false

/-- The NEW `monotonic × concurrent` §6.8 collision as a `SoundnessCollisionSchema`: concurrency demands
sequencing-freedom, mutation modes may or may not be concurrency-safe. -/
def monotonicConcurrentSchema : SoundnessCollisionSchema where
  Demand := ConcurrencyGrade
  Capability := MutationGrade
  isStrongDemand := ConcurrencyGrade.isConcurrent
  preservesInvariant := MutationGrade.isConcurrencySafe

/-- ★ **The §6.8 `monotonic × concurrent` collision.**  A `monotonic` mutation (forward-only in a partial order)
is NOT jointly consistent with unsynchronized concurrent access: two threads committing out of order violate the
monotone invariant.  The second §6.8 collision, drawn from a different pair of dimensions than #1021 yet the SAME
generic theorem. -/
theorem concurrentCollidesWithMonotonic :
    ¬ monotonicConcurrentSchema.IsConsistent ConcurrencyGrade.concurrent MutationGrade.monotonic :=
  (monotonicConcurrentSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

/-- The `appendOnly` twin: concurrent tail-appends race on the tail pointer. -/
theorem concurrentCollidesWithAppendOnly :
    ¬ monotonicConcurrentSchema.IsConsistent ConcurrencyGrade.concurrent MutationGrade.appendOnly :=
  (monotonicConcurrentSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

/-- The `readWrite` twin: arbitrary concurrent mutation is the classic data race. -/
theorem concurrentCollidesWithReadWrite :
    ¬ monotonicConcurrentSchema.IsConsistent ConcurrencyGrade.concurrent MutationGrade.readWrite :=
  (monotonicConcurrentSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

/-- **The collision is SPECIFIC**: `immutable` (read-only) IS sound under concurrent access — concurrent reads
never conflict. -/
theorem concurrentConsistentWithImmutable :
    monotonicConcurrentSchema.IsConsistent ConcurrencyGrade.concurrent MutationGrade.immutable :=
  fun _ => rfl

/-- **No demand, no collision**: a `sequential` (synchronized) access is consistent with EVERY mutation mode —
the collision is purely a property of demanding UNSYNCHRONIZED concurrency. -/
theorem sequentialConsistentWithEveryMutation (mutation : MutationGrade) :
    monotonicConcurrentSchema.IsConsistent ConcurrencyGrade.sequential mutation :=
  fun absurdFlag => Bool.noConfusion absurdFlag

end FX1Poly.Modal
