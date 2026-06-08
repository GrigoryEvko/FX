import FX1Poly.Modal.SoundnessCollisionCatalog

/-! # FX1Poly/Modal/SoundnessCollisionCatalogComplete
    — the last three §6.8 entries; the entire nine-entry collision catalog is now mechanized

`SoundnessCollisionSchema` (#1022) abstracted the §6.8 collision form; `SoundnessCollisionCatalog`
(#1028) classified the catalog into CO-OCCURRENCE vs SCOPING/CONTROL-REFINED shapes and mechanized
`ghost × runtime` (co-occurrence) plus `borrow × Async` / `borrow × unscoped spawn` (control-refined).
With `PrecisionOverflowCollision` (#1021, `decimal × overflow`), the second `SoundnessCollisionSchema`
instance (#1022, `monotonic × concurrent`), and the three-way `classified × async × session`
(#1026/#1027), six of CLAUDE.md's nine §6.8 entries were mechanized.

This file mechanizes the LAST THREE, completing the catalog.  All three are CONTROL-REFINED — the
collision fires only when a secret CONTROLS an observable (the §12.2/§12.5 implicit-flow / constant-time
discipline), not on mere co-occurrence:

  * **`CT × Async`** — `constantTimeAsyncSchema`: a constant-time guarantee (§12.5) is broken when async
    scheduling makes the timing SECRET-DEPENDENT (the scheduler's completion order leaks the secret).
    `constantTimeCollidesWithSecretDependentAsync` (★) is the collision;
    `constantTimeConsistentWithSecretIndependentAsync` shows async with secret-INDEPENDENT timing is
    fine — async per se does not break CT.
  * **`classified × Fail`** — `classifiedFailSchema`: a secret is leaked when a secret-CONTROLLED
    failure (§4.9 `Fail` effect) is OBSERVABLE to an unclassified observer (implicit flow through the
    exception, §12.2).  `secretControlledFailureCollidesWithObservableFailure` (★) is the collision;
    `secretControlledFailureConsistentWithClassifiedFailure` shows a contained (classified) failure is
    fine.
  * **`CT × Fail on secret`** — `constantTimeFailOnSecretSchema`: a constant-time guarantee is broken by
    a secret-DEPENDENT failure PATH (success vs failure observably differ).
    `constantTimeCollidesWithSecretDependentFailure` (★) is the collision;
    `constantTimeConsistentWithSecretIndependentFailure` shows a secret-independent failure path is
    fine.

  * **`sec68RemainingCatalogControlRefined` (★)** — the capstone: all three new entries co-occur
    SOUNDLY when the control capability is withheld (secret-independent timing / contained failure /
    secret-independent failure path), confirming they belong to the control-refined family — exactly
    like `classified × async × session` (#1026/#1027) and `borrow × Async` / `borrow × spawn` (#1028).

With these, the entire nine-entry §6.8 catalog is mechanized and classified: three co-occurrence
collisions (`decimal × overflow`, `monotonic × concurrent`, `ghost × runtime`) and six control-refined
collisions (`classified × async × session`, `borrow × Async`, `borrow × unscoped spawn`, `CT × Async`,
`classified × Fail`, `CT × Fail on secret`).

## Honest scope boundary

These are COMBINE-time joint-consistency CONSTRAINTS over dimension-grade pairs — the algebraic face of
§6.8.  Each schema IS the constraint the term-level checker enforces; the control demand
(`isConstantTimeRequired` / `isSecretControllingFailure`) is the property the §12.2 implicit-flow and
§12.5 constant-time analyses discharge per-term.

## Zero-axiom verification

Every collision is `(notConsistent_iff _ _).mpr ⟨rfl, rfl⟩`; every consistency is `fun _ => rfl`
(invariant preserved) or `Bool.noConfusion` (demand absent); the capstone pairs the three control
witnesses.  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-! ## `CT × Async` — constant-time broken by secret-dependent async timing -/

/-- The constant-time guarantee demand (§12.5): `constantTimeRequired` demands a trace independent of
secrets; `variableTimeOk` does not. -/
inductive ConstantTimeDemand where
  | constantTimeRequired
  | variableTimeOk
  deriving DecidableEq

/-- The strong-demand predicate: requiring constant time is the demanding grade. -/
def ConstantTimeDemand.isConstantTimeRequired : ConstantTimeDemand → Bool
  | .constantTimeRequired => true
  | .variableTimeOk => false

/-- The async timing behaviour: does the async scheduling make the observable timing depend on a
secret?  `secretIndependentTiming` preserves the CT invariant; `secretDependentTiming` does not. -/
inductive AsyncTimingBehavior where
  | secretDependentTiming
  | secretIndependentTiming
  deriving DecidableEq

/-- Does the async timing preserve constant-time's secret-independence invariant?  Only
`secretIndependentTiming` does. -/
def AsyncTimingBehavior.isSecretIndependent : AsyncTimingBehavior → Bool
  | .secretIndependentTiming => true
  | .secretDependentTiming => false

/-- The §6.8 `CT × Async` collision as a `SoundnessCollisionSchema`: the constant-time demand against
the async timing behaviour. -/
def constantTimeAsyncSchema : SoundnessCollisionSchema where
  Demand := ConstantTimeDemand
  Capability := AsyncTimingBehavior
  isStrongDemand := ConstantTimeDemand.isConstantTimeRequired
  preservesInvariant := AsyncTimingBehavior.isSecretIndependent

/-- ★ **The `CT × Async` collision.**  A constant-time guarantee is broken when async scheduling makes
the timing secret-dependent — the scheduler's completion order leaks the secret. -/
theorem constantTimeCollidesWithSecretDependentAsync :
    ¬ constantTimeAsyncSchema.IsConsistent ConstantTimeDemand.constantTimeRequired
        AsyncTimingBehavior.secretDependentTiming :=
  (constantTimeAsyncSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

/-- **Control-refinement of `CT × Async`.**  Async with secret-INDEPENDENT timing is consistent EVEN
under a constant-time demand — async per se does not break CT, only secret-dependent async timing
does. -/
theorem constantTimeConsistentWithSecretIndependentAsync :
    constantTimeAsyncSchema.IsConsistent ConstantTimeDemand.constantTimeRequired
      AsyncTimingBehavior.secretIndependentTiming :=
  fun _ => rfl

/-- **No demand, no collision**: code that does not require constant time is consistent with every
async timing behaviour. -/
theorem variableTimeConsistentWithAnyAsync (timing : AsyncTimingBehavior) :
    constantTimeAsyncSchema.IsConsistent ConstantTimeDemand.variableTimeOk timing :=
  fun absurdFlag => Bool.noConfusion absurdFlag

/-! ## `classified × Fail` — secret leaked by a secret-controlled observable failure -/

/-- The classified-flow demand: does a secret CONTROL whether a failure occurs (§12.2 implicit flow)?
`secretControlsFailure` is the demanding grade; `failureSecretIndependent` is not. -/
inductive ClassifiedFailureDemand where
  | secretControlsFailure
  | failureSecretIndependent
  deriving DecidableEq

/-- The strong-demand predicate: a secret controlling whether a failure fires is the demanding grade. -/
def ClassifiedFailureDemand.isSecretControllingFailure : ClassifiedFailureDemand → Bool
  | .secretControlsFailure => true
  | .failureSecretIndependent => false

/-- The failure observability: is the `fail(e)` observable to an unclassified observer, or contained
(classified)?  `failureClassified` keeps the secret; `observableToUnclassified` leaks it. -/
inductive FailureObservability where
  | observableToUnclassified
  | failureClassified
  deriving DecidableEq

/-- Is the failure contained (not leaking the controlling secret)?  Only `failureClassified` is. -/
def FailureObservability.isFailureContained : FailureObservability → Bool
  | .failureClassified => true
  | .observableToUnclassified => false

/-- The §6.8 `classified × Fail` collision as a `SoundnessCollisionSchema`: the secret-controls-failure
demand against the failure observability. -/
def classifiedFailSchema : SoundnessCollisionSchema where
  Demand := ClassifiedFailureDemand
  Capability := FailureObservability
  isStrongDemand := ClassifiedFailureDemand.isSecretControllingFailure
  preservesInvariant := FailureObservability.isFailureContained

/-- ★ **The `classified × Fail` collision.**  A secret is leaked when a secret-CONTROLLED failure is
OBSERVABLE to an unclassified observer — an implicit flow through the exception's presence (§12.2). -/
theorem secretControlledFailureCollidesWithObservableFailure :
    ¬ classifiedFailSchema.IsConsistent ClassifiedFailureDemand.secretControlsFailure
        FailureObservability.observableToUnclassified :=
  (classifiedFailSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

/-- **Control-refinement of `classified × Fail`.**  A secret-controlled failure that is CONTAINED
(classified — not observable to unclassified code) is consistent: the secret does not leak. -/
theorem secretControlledFailureConsistentWithClassifiedFailure :
    classifiedFailSchema.IsConsistent ClassifiedFailureDemand.secretControlsFailure
      FailureObservability.failureClassified :=
  fun _ => rfl

/-- **No demand, no collision**: a failure whose occurrence is secret-INDEPENDENT is consistent with
every observability — the collision is purely about the SECRET controlling the failure. -/
theorem secretIndependentFailureConsistentWithAnyObservability (observability : FailureObservability) :
    classifiedFailSchema.IsConsistent ClassifiedFailureDemand.failureSecretIndependent observability :=
  fun absurdFlag => Bool.noConfusion absurdFlag

/-! ## `CT × Fail on secret` — constant-time broken by a secret-dependent failure path -/

/-- The failure-path behaviour: does whether the `fail(e)` fires depend on a secret?
`secretIndependentFailure` preserves CT (success and failure paths are observably uniform);
`secretDependentFailure` does not. -/
inductive FailurePathBehavior where
  | secretDependentFailure
  | secretIndependentFailure
  deriving DecidableEq

/-- Does the failure path preserve constant-time's secret-independence?  Only
`secretIndependentFailure` does. -/
def FailurePathBehavior.isSecretIndependent : FailurePathBehavior → Bool
  | .secretIndependentFailure => true
  | .secretDependentFailure => false

/-- The §6.8 `CT × Fail on secret` collision as a `SoundnessCollisionSchema`: the constant-time demand
against the failure-path behaviour. -/
def constantTimeFailOnSecretSchema : SoundnessCollisionSchema where
  Demand := ConstantTimeDemand
  Capability := FailurePathBehavior
  isStrongDemand := ConstantTimeDemand.isConstantTimeRequired
  preservesInvariant := FailurePathBehavior.isSecretIndependent

/-- ★ **The `CT × Fail on secret` collision.**  A constant-time guarantee is broken by a
secret-DEPENDENT failure path — success and failure paths observably differ, so whether the secret
triggers the failure leaks through the trace. -/
theorem constantTimeCollidesWithSecretDependentFailure :
    ¬ constantTimeFailOnSecretSchema.IsConsistent ConstantTimeDemand.constantTimeRequired
        FailurePathBehavior.secretDependentFailure :=
  (constantTimeFailOnSecretSchema.notConsistent_iff _ _).mpr ⟨rfl, rfl⟩

/-- **Control-refinement of `CT × Fail on secret`.**  A secret-INDEPENDENT failure path is consistent
under a constant-time demand — failure per se does not break CT, only a secret-dependent failure
path. -/
theorem constantTimeConsistentWithSecretIndependentFailure :
    constantTimeFailOnSecretSchema.IsConsistent ConstantTimeDemand.constantTimeRequired
      FailurePathBehavior.secretIndependentFailure :=
  fun _ => rfl

/-! ## Capstone: the three new entries complete the control-refined family -/

/-- ★ **The last three §6.8 entries are CONTROL-REFINED.**  Each co-occurs SOUNDLY when the control
capability is withheld — secret-independent async timing, a contained (classified) failure, and a
secret-independent failure path are each consistent with their guarantee demand.  So `CT × Async`,
`classified × Fail`, and `CT × Fail on secret` join the control-refined family alongside
`classified × async × session` (#1026/#1027) and `borrow × Async` / `borrow × unscoped spawn` (#1028).

With these, the entire nine-entry §6.8 catalog is mechanized: three co-occurrence collisions and six
control-refined ones. -/
theorem sec68RemainingCatalogControlRefined :
    constantTimeAsyncSchema.IsConsistent ConstantTimeDemand.constantTimeRequired
      AsyncTimingBehavior.secretIndependentTiming ∧
    classifiedFailSchema.IsConsistent ClassifiedFailureDemand.secretControlsFailure
      FailureObservability.failureClassified ∧
    constantTimeFailOnSecretSchema.IsConsistent ConstantTimeDemand.constantTimeRequired
      FailurePathBehavior.secretIndependentFailure :=
  ⟨constantTimeConsistentWithSecretIndependentAsync,
   secretControlledFailureConsistentWithClassifiedFailure,
   constantTimeConsistentWithSecretIndependentFailure⟩

end FX1Poly.Modal
