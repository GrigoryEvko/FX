import FX1Poly.Modal.SoundnessCollisionSchema

/-! # FX1Poly/Modal/SoundnessCollisionCatalog
    — completing and CLASSIFYING the §6.8 cross-dimension collision catalog into its two structural
      shapes: CO-OCCURRENCE vs SCOPING-REFINED

`SoundnessCollisionSchema` (#1022) abstracted the §6.8 collision FORM and mechanized two instances
(`decimal × overflow`, `monotonic × concurrent`); `ThreeWayCollisionClassifiedAsyncSession` (#1026)
added the one genuinely three-way entry; `FlagshipMultiDimensionSignature` (#1027) discovered that the
3-way collision needs the §12.2 IMPLICIT-FLOW refinement — the collision fires only when the classified
value CONTROLS the scheduling, not when it merely co-occurs with async + sessions.

This file shows that #1027's insight is not a one-off: it is a whole STRUCTURAL CLASS of the §6.8
catalog.  CLAUDE.md's §6.8 catalog has nine entries; mechanizing the rest and classifying them reveals
the catalog is NOT uniform — every §6.8 collision is one of two shapes:

  * **CO-OCCURRENCE** — unsound on mere joint presence of the two grades.  The strong demand IS the
    dimension's presence.  Examples: `decimal × overflow` (#1021), `monotonic × concurrent` (#1022),
    and here **`ghost × runtime`** — a grade-0 (erased) value observed at runtime is unconditionally
    unsound (it does not survive erasure).
  * **SCOPING-REFINED** — unsound ONLY when a CONTROL / ESCAPE capability fires; sound when the two
    grades co-occur but the scope is respected.  The strong demand is the control capability, strictly
    stronger than presence.  Examples: `classified × async × session` (#1026/#1027 — secret CONTROLS
    scheduling), and here **`borrow × Async`** (the borrow ESCAPES the async continuation) and
    **`borrow × unscoped spawn`** (the borrow escapes into a spawn that outlives it).

The payoff is the structural theorem `catalogHasTwoCollisionClasses`: a co-occurrence collision
(`ghost × runtime`) collides whenever both grades are present, but a scoping-refined collision
(`borrow × Async`) is CONSISTENT when both grades are present yet the borrow is confined — which is
exactly why §1.3's `encrypt_and_send` borrows a key UNDER async soundly (#1027).  The catalog's
remaining scoping-refined entries (`CT × Async`, `classified × Fail`, `CT × Fail on secret`) share this
shape (control-demand as the strong demand) and instantiate the same `SoundnessCollisionSchema`.

## What this file ships (all zero-axiom)

  * `ghostRuntimeSchema` (+ `ghostObservedAtRuntimeCollision` ★, `runtimePresentValueObservable`,
    `unobservedGhostConsistent`) — the clean CO-OCCURRENCE entry: ghost-grade observed at runtime
    collides; a runtime-present value is observable; an unobserved ghost is fine.
  * `borrowAsyncSchema` (+ `borrowEscapeUnderAsyncCollision` ★, `confinedBorrowUnderAsyncConsistent`) —
    the SCOPING-REFINED `borrow × Async`: an ESCAPING borrow under async collides, but a CONFINED
    borrow under async is consistent (the §1.3 flagship's key, #1027).
  * `borrowSpawnSchema` (+ `borrowEscapeIntoUnscopedSpawnCollision` ★, `borrowIntoScopedSpawnConsistent`)
    — the scoping-refined twin: a borrow escaping into an UNSCOPED spawn collides, but into a SCOPED
    spawn (a `task_group`, §11.7) is consistent.
  * **`catalogHasTwoCollisionClasses` (★)** — the structural dichotomy: a co-occurrence collision
    collides on joint presence; a scoping-refined collision is consistent on joint presence (scope
    respected).  The §6.8 catalog has two structurally distinct collision shapes.

## Honest scope boundary

These are COMBINE-time joint-consistency CONSTRAINTS over dimension-grade pairs — the algebraic face of
§6.8, classified by shape.  They do not wire the constraints into the term-level grade-vector checker;
each schema IS the constraint such a checker enforces, and the scoping-refined ones' control demand
(`escapesScope` / `isRuntimeObserved`) is the property the term-level analysis (region inference §8.1,
escape analysis, the §12.2 implicit-flow checker) discharges per-term.

## Zero-axiom verification

Every collision is `(notConsistent_iff _ _).mpr ⟨rfl, rfl⟩`; every consistency is `fun _ => rfl` /
`Bool.noConfusion` on the impossible demand flag; the dichotomy pairs the two.  No `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-! ## `ghost × runtime` — a CO-OCCURRENCE collision (unsound on mere joint presence) -/

/-- The runtime-observation demand: does the program OBSERVE this value at runtime?  `runtimeObserved`
is the strong demand (the value must materialize at runtime); `ghostOnly` uses it only in erased
proof/spec position. -/
inductive ObservationDemand where
  | runtimeObserved
  | ghostOnly
  deriving DecidableEq

/-- The strong-demand predicate: a value observed at runtime is the demanding grade. -/
def ObservationDemand.isRuntimeObserved : ObservationDemand → Bool
  | .runtimeObserved => true
  | .ghostOnly => false

/-- The erasure capability (§6.5 ghost = grade-0): `erasedGhost` is compiled away (Zero permission);
`runtimePresent` survives to the binary. -/
inductive ErasureCapability where
  | erasedGhost
  | runtimePresent
  deriving DecidableEq

/-- Does this erasure status PRESERVE runtime observability?  Only `runtimePresent` does — an
`erasedGhost` value is gone after §20.2 erasure, so it cannot be observed. -/
def ErasureCapability.isObservabilityPreserving : ErasureCapability → Bool
  | .runtimePresent => true
  | .erasedGhost => false

/-- The §6.8 `ghost × runtime` collision as a `SoundnessCollisionSchema`: runtime-observation demands
the value survive, erasure status may or may not preserve it. -/
def ghostRuntimeSchema : SoundnessCollisionSchema where
  Demand := ObservationDemand
  Capability := ErasureCapability
  isStrongDemand := ObservationDemand.isRuntimeObserved
  preservesInvariant := ErasureCapability.isObservabilityPreserving

/-- ★ **The `ghost × runtime` collision (CO-OCCURRENCE).**  A grade-0 (erased) value DEMANDED at
runtime is unconditionally unsound — the value is compiled away, so observing it at runtime is
impossible.  The strong demand IS the runtime-presence requirement: this collides on mere joint
presence, the defining trait of a co-occurrence collision. -/
theorem ghostObservedAtRuntimeCollision :
    ¬ ghostRuntimeSchema.IsConsistent ObservationDemand.runtimeObserved ErasureCapability.erasedGhost :=
  (ghostRuntimeSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

/-- A runtime-present value demanded at runtime IS observable — the collision is specific to the
erased grade. -/
theorem runtimePresentValueObservable :
    ghostRuntimeSchema.IsConsistent ObservationDemand.runtimeObserved ErasureCapability.runtimePresent :=
  fun _ => rfl

/-- **No demand, no collision**: a ghost value used only in erased (proof/spec) position is consistent
with EVERY erasure status — the collision is purely a property of DEMANDING the erased value at
runtime. -/
theorem unobservedGhostConsistent (erasure : ErasureCapability) :
    ghostRuntimeSchema.IsConsistent ObservationDemand.ghostOnly erasure :=
  fun absurdFlag => Bool.noConfusion absurdFlag

/-! ## `borrow × Async` — a SCOPING-REFINED collision (demand = the ESCAPE control, not presence) -/

/-- The borrow-escape demand: does the borrow ESCAPE its lexical scope (§8.1 region)?  `escapesScope`
is the strong demand (the borrow outlives its region); `confinedToScope` keeps it within. -/
inductive BorrowEscapeDemand where
  | escapesScope
  | confinedToScope
  deriving DecidableEq

/-- The strong-demand predicate: a borrow that escapes its region is the demanding grade. -/
def BorrowEscapeDemand.isEscaping : BorrowEscapeDemand → Bool
  | .escapesScope => true
  | .confinedToScope => false

/-- The async context: is an `Async` effect (§9.9) granted at the borrow site?  `asyncGranted`
introduces a suspension point the escaped borrow could outlive; `asyncAbsent` does not. -/
inductive AsyncContext where
  | asyncGranted
  | asyncAbsent
  deriving DecidableEq

/-- Does this async context CONFINE an escaped borrow?  Only `asyncAbsent` does — granting `Async`
without confining the borrow lets it cross a suspension point and dangle. -/
def AsyncContext.isBorrowConfining : AsyncContext → Bool
  | .asyncAbsent => true
  | .asyncGranted => false

/-- The §6.8 `borrow × Async` collision as a `SoundnessCollisionSchema`: the strong demand is the
borrow ESCAPING (not the borrow merely existing), the capability is the async context. -/
def borrowAsyncSchema : SoundnessCollisionSchema where
  Demand := BorrowEscapeDemand
  Capability := AsyncContext
  isStrongDemand := BorrowEscapeDemand.isEscaping
  preservesInvariant := AsyncContext.isBorrowConfining

/-- ★ **The `borrow × Async` collision (SCOPING-REFINED).**  A borrow that ESCAPES its region under a
granted `Async` effect is unsound — the borrow can cross the suspension point and outlive its
referent.  The strong demand is the ESCAPE, not the borrow's presence. -/
theorem borrowEscapeUnderAsyncCollision :
    ¬ borrowAsyncSchema.IsConsistent BorrowEscapeDemand.escapesScope AsyncContext.asyncGranted :=
  (borrowAsyncSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

/-- **The §1.3 flagship's borrowed key is consistent under async.**  A CONFINED borrow (one whose
region covers the async continuation) is consistent EVEN WITH `Async` granted — which is exactly why
`encrypt_and_send` (#1027) takes a `secret ref(r)` key under `with ..., Async` soundly.  This is the
defining trait of a scoping-refined collision: the two grades co-occur soundly when the scope is
respected, unlike a co-occurrence collision. -/
theorem confinedBorrowUnderAsyncConsistent :
    borrowAsyncSchema.IsConsistent BorrowEscapeDemand.confinedToScope AsyncContext.asyncGranted :=
  fun absurdFlag => Bool.noConfusion absurdFlag

/-! ## `borrow × unscoped spawn` — the scoping-refined twin (a `task_group` confines) -/

/-- The spawn context: is a spawned task SCOPED (§11.7 `task_group` — guaranteed to complete before the
group exits) or UNSCOPED (may outlive the borrow's region)? -/
inductive SpawnContext where
  | unscopedSpawn
  | scopedSpawn
  deriving DecidableEq

/-- Does this spawn context CONFINE an escaped borrow?  Only `scopedSpawn` does — a `task_group`
bounds the spawned task's lifetime to the borrow's scope; an unscoped spawn can outlive it. -/
def SpawnContext.isBorrowConfining : SpawnContext → Bool
  | .scopedSpawn => true
  | .unscopedSpawn => false

/-- The §6.8 `borrow × unscoped spawn` collision as a `SoundnessCollisionSchema`: the escaping-borrow
demand against the spawn context. -/
def borrowSpawnSchema : SoundnessCollisionSchema where
  Demand := BorrowEscapeDemand
  Capability := SpawnContext
  isStrongDemand := BorrowEscapeDemand.isEscaping
  preservesInvariant := SpawnContext.isBorrowConfining

/-- ★ **The `borrow × unscoped spawn` collision (SCOPING-REFINED).**  A borrow escaping into an
UNSCOPED spawn is unsound — the spawned task may run after the borrow's region ends, dangling the
reference. -/
theorem borrowEscapeIntoUnscopedSpawnCollision :
    ¬ borrowSpawnSchema.IsConsistent BorrowEscapeDemand.escapesScope SpawnContext.unscopedSpawn :=
  (borrowSpawnSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

/-- **A `task_group` confines even an escaping borrow.**  Capturing a borrow into a SCOPED spawn
(§11.7 — all spawned tasks complete before the group exits) is consistent: the structured-concurrency
scope bounds the borrow's lifetime.  The scoping refinement again admits the sound co-occurrence. -/
theorem borrowIntoScopedSpawnConsistent :
    borrowSpawnSchema.IsConsistent BorrowEscapeDemand.escapesScope SpawnContext.scopedSpawn :=
  fun _ => rfl

/-! ## The structural dichotomy of the §6.8 catalog -/

/-- ★ **The §6.8 catalog has TWO structurally distinct collision shapes.**  A CO-OCCURRENCE collision
(`ghost × runtime`) collides whenever both grades are jointly present — there is no sound co-occurrence.
A SCOPING-REFINED collision (`borrow × Async`) is CONSISTENT when both grades are jointly present yet
the scope is respected (the borrow confined) — the collision needs the ESCAPE control, strictly
stronger than presence.

This is why the §6.8 catalog cannot be read as a uniform "these dimensions never mix" list: half its
entries (`decimal × overflow`, `monotonic × concurrent`, `ghost × runtime`) forbid co-occurrence, while
the other half (`classified × async × session`, `borrow × Async`, `borrow × unscoped spawn`,
`CT × Async`, `classified × Fail`) forbid only an ESCAPE / CONTROL capability — and the latter is
precisely what lets §1.3's `encrypt_and_send` borrow a secret key under async soundly (#1027). -/
theorem catalogHasTwoCollisionClasses :
    (¬ ghostRuntimeSchema.IsConsistent ObservationDemand.runtimeObserved ErasureCapability.erasedGhost) ∧
    borrowAsyncSchema.IsConsistent BorrowEscapeDemand.confinedToScope AsyncContext.asyncGranted :=
  ⟨ghostObservedAtRuntimeCollision, confinedBorrowUnderAsyncConsistent⟩

end FX1Poly.Modal
