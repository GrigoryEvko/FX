import LeanFX.Mode.Composable

/-! # Concrete FX collision catalog.

The abstract composability substrate is intentionally generic.  This
file records the finite named collision atoms currently represented in
the Lean foundation and instantiates a decidable composability category
whose forbidden traces mirror the catalog in `fx_design.md` §6.8.
-/

namespace LeanFX.Mode

/-- Dimension atoms that participate in the initial FX collision
catalog.  These are not full grades yet; they are the finite names
needed to make forbidden trace composition explicit. -/
inductive FxCollisionAtom : Type
  | classified
  | fail
  | borrow
  | async
  | constantTime
  | secret
  | ghost
  | runtime
  | monotonic
  | concurrent
  | decimal
  | overflowWrap
  | unscopedSpawn
  | session
  | stalenessPositive
  | capability
  | replay
  | linear
  deriving DecidableEq, Repr

/-- A finite trace of dimension atoms.  Composition appends traces;
forbidden composition means the combined trace triggers one of the
catalogued §6.8 guards. -/
abbrev FxCollisionTrace : Type :=
  List FxCollisionAtom

namespace FxCollisionTrace

/-- Does the trace contain a named collision atom? -/
def hasAtom (trace : FxCollisionTrace) (needleAtom : FxCollisionAtom) : Bool :=
  trace.any fun traceAtom =>
    traceAtom == needleAtom

/-- A binary rule is present when both named atoms occur in the trace. -/
def hasBinaryRule
    (trace : FxCollisionTrace)
    (firstAtom secondAtom : FxCollisionAtom) : Bool :=
  trace.hasAtom firstAtom && trace.hasAtom secondAtom

/-- A ternary rule is present when all three named atoms occur in the
trace. -/
def hasTernaryRule
    (trace : FxCollisionTrace)
    (firstAtom secondAtom thirdAtom : FxCollisionAtom) : Bool :=
  trace.hasAtom firstAtom &&
    trace.hasAtom secondAtom &&
      trace.hasAtom thirdAtom

/-- I002: classified x Fail. -/
def hasClassifiedFailCollision (trace : FxCollisionTrace) : Bool :=
  trace.hasBinaryRule .classified .fail

/-- L002: borrow x Async. -/
def hasBorrowAsyncCollision (trace : FxCollisionTrace) : Bool :=
  trace.hasBinaryRule .borrow .async

/-- E044: constant-time x Async. -/
def hasConstantTimeAsyncCollision (trace : FxCollisionTrace) : Bool :=
  trace.hasBinaryRule .constantTime .async

/-- I003: constant-time x Fail on secret. -/
def hasConstantTimeSecretFailCollision (trace : FxCollisionTrace) : Bool :=
  trace.hasTernaryRule .constantTime .secret .fail

/-- M012: monotonic/append-only x concurrent. -/
def hasMonotonicConcurrentCollision (trace : FxCollisionTrace) : Bool :=
  trace.hasBinaryRule .monotonic .concurrent

/-- P002: ghost x runtime position. -/
def hasGhostRuntimeCollision (trace : FxCollisionTrace) : Bool :=
  trace.hasBinaryRule .ghost .runtime

/-- I004: classified x async x session. -/
def hasClassifiedAsyncSessionCollision (trace : FxCollisionTrace) : Bool :=
  trace.hasTernaryRule .classified .async .session

/-- N002: exact decimal x overflow(wrap). -/
def hasDecimalOverflowWrapCollision (trace : FxCollisionTrace) : Bool :=
  trace.hasBinaryRule .decimal .overflowWrap

/-- L003: borrow x unscoped spawn. -/
def hasBorrowUnscopedSpawnCollision (trace : FxCollisionTrace) : Bool :=
  trace.hasBinaryRule .borrow .unscopedSpawn

/-- M011 reduction guard from Appendix F: linear value may leak on
Fail/Exn path unless cleanup is registered. -/
def hasLinearFailCleanupCollision (trace : FxCollisionTrace) : Bool :=
  trace.hasBinaryRule .linear .fail

/-- S010: positive staleness x constant-time observation. -/
def hasStalenessConstantTimeCollision (trace : FxCollisionTrace) : Bool :=
  trace.hasBinaryRule .stalenessPositive .constantTime

/-- S011: capability x replay without replay-stable representation. -/
def hasCapabilityReplayCollision (trace : FxCollisionTrace) : Bool :=
  trace.hasBinaryRule .capability .replay

/-- Does the trace trigger any currently catalogued FX composition
guard from `fx_design.md` §6.8 plus the Appendix F linear-Fail
reduction guard? -/
def hasAnyCollision (trace : FxCollisionTrace) : Bool :=
  trace.hasClassifiedFailCollision ||
    trace.hasBorrowAsyncCollision ||
      trace.hasConstantTimeAsyncCollision ||
        trace.hasConstantTimeSecretFailCollision ||
          trace.hasMonotonicConcurrentCollision ||
            trace.hasGhostRuntimeCollision ||
              trace.hasClassifiedAsyncSessionCollision ||
                trace.hasDecimalOverflowWrapCollision ||
                  trace.hasBorrowUnscopedSpawnCollision ||
                    trace.hasLinearFailCleanupCollision ||
                      trace.hasStalenessConstantTimeCollision ||
                        trace.hasCapabilityReplayCollision

/-- Admissible trace composition: the combined trace triggers no
catalogued collision. -/
def IsComposable (leftTrace rightTrace : FxCollisionTrace) : Prop :=
  hasAnyCollision (leftTrace ++ rightTrace) = false

/-- Local append-right-identity proof kept axiom-free instead of using
the standard-library theorem, whose transitive audit includes
`propext` in this toolchain. -/
theorem append_nil_axiomFree :
    ∀ trace : FxCollisionTrace, trace ++ [] = trace
  | [] => rfl
  | traceAtom :: remainingTrace => by
      exact congrArg (List.cons traceAtom)
        (append_nil_axiomFree remainingTrace)

/-- Local append-associativity proof kept axiom-free instead of using
the standard-library theorem, whose transitive audit includes
`propext` in this toolchain. -/
theorem append_assoc_axiomFree :
    ∀ firstTrace secondTrace thirdTrace : FxCollisionTrace,
      (firstTrace ++ secondTrace) ++ thirdTrace =
        firstTrace ++ (secondTrace ++ thirdTrace)
  | [], _, _ => rfl
  | traceAtom :: remainingTrace, secondTrace, thirdTrace => by
      exact congrArg (List.cons traceAtom)
        (append_assoc_axiomFree remainingTrace secondTrace thirdTrace)

/-- Decidable composability without routing through generic proposition
extensionality machinery. -/
def isComposableDecidable
    (leftTrace rightTrace : FxCollisionTrace) :
    Decidable (IsComposable leftTrace rightTrace) :=
  match collisionCheck :
      hasAnyCollision (leftTrace ++ rightTrace) with
  | false =>
      isTrue (by
        unfold IsComposable
        exact collisionCheck)
  | true =>
      isFalse (by
        unfold IsComposable
        rw [collisionCheck]
        intro impossibleEquality
        cases impossibleEquality)

/-- Collision traces form a one-object category with append as
composition and a decidable composability predicate. -/
def composableCategory : ComposableTwoCellCat where
  ModeCarrier := Unit
  Modality := fun _ _ => FxCollisionTrace
  idMod := fun _ => []
  compMod := fun leftTrace rightTrace => leftTrace ++ rightTrace
  idLeft := by
    intro sourceMode targetMode trace
    rfl
  idRight := by
    intro sourceMode targetMode trace
    exact append_nil_axiomFree trace
  compAssoc := by
    intro firstMode secondMode thirdMode fourthMode
    intro firstTrace secondTrace thirdTrace
    exact append_assoc_axiomFree firstTrace secondTrace thirdTrace
  TwoCell := fun firstTrace secondTrace =>
    firstTrace = secondTrace
  twoCellRefl := fun _ => rfl
  twoCellTrans := fun firstEquality secondEquality =>
    firstEquality.trans secondEquality
  twoCellWhisker := by
    intro sourceMode middleMode targetMode
    intro firstLeftTrace firstRightTrace
    intro secondLeftTrace secondRightTrace
    intro firstEquality secondEquality
    cases firstEquality
    cases secondEquality
    rfl
  Composable := fun leftTrace rightTrace =>
    IsComposable leftTrace rightTrace
  isComposableDecidable := fun leftTrace rightTrace =>
    isComposableDecidable leftTrace rightTrace

/-- Singleton trace helper for smoke tests and later finite instances. -/
def singleton (atom : FxCollisionAtom) : FxCollisionTrace :=
  [atom]

/-- A trace collision is rejected by the composability predicate. -/
theorem not_composable_of_hasAnyCollision_true
    (leftTrace rightTrace : FxCollisionTrace)
    (collisionWasFound : hasAnyCollision (leftTrace ++ rightTrace) = true) :
    ¬ IsComposable leftTrace rightTrace := by
  unfold IsComposable
  rw [collisionWasFound]
  intro impossibleEquality
  cases impossibleEquality

/-- A non-colliding singleton pair can be composed. -/
example :
    IsComposable (singleton .classified) (singleton .borrow) :=
  rfl

/-- I002: classified x Fail is forbidden. -/
example :
    ¬ IsComposable (singleton .classified) (singleton .fail) :=
  not_composable_of_hasAnyCollision_true
    (singleton .classified) (singleton .fail) rfl

/-- L002: borrow x Async is forbidden. -/
example :
    ¬ IsComposable (singleton .borrow) (singleton .async) :=
  not_composable_of_hasAnyCollision_true
    (singleton .borrow) (singleton .async) rfl

/-- E044: constant-time x Async is forbidden. -/
example :
    ¬ IsComposable (singleton .constantTime) (singleton .async) :=
  not_composable_of_hasAnyCollision_true
    (singleton .constantTime) (singleton .async) rfl

/-- I003: constant-time x Fail on secret is forbidden as a ternary
guard, while the weaker constant-time x Fail pair alone is not. -/
example :
    IsComposable (singleton .constantTime) (singleton .fail) :=
  rfl

/-- I003: constant-time x Fail on secret is forbidden. -/
example :
    ¬ IsComposable [.constantTime, .secret] [.fail] :=
  not_composable_of_hasAnyCollision_true
    [.constantTime, .secret] [.fail] rfl

/-- M012: monotonic x concurrent is forbidden. -/
example :
    ¬ IsComposable (singleton .monotonic) (singleton .concurrent) :=
  not_composable_of_hasAnyCollision_true
    (singleton .monotonic) (singleton .concurrent) rfl

/-- P002: ghost x runtime is forbidden. -/
example :
    ¬ IsComposable (singleton .ghost) (singleton .runtime) :=
  not_composable_of_hasAnyCollision_true
    (singleton .ghost) (singleton .runtime) rfl

/-- I004: classified x async x session is forbidden as a ternary
guard, while classified x async alone is not. -/
example :
    IsComposable (singleton .classified) (singleton .async) :=
  rfl

/-- I004: classified x async x session is forbidden. -/
example :
    ¬ IsComposable [.classified, .async] [.session] :=
  not_composable_of_hasAnyCollision_true
    [.classified, .async] [.session] rfl

/-- N002: decimal x overflow(wrap) is forbidden. -/
example :
    ¬ IsComposable (singleton .decimal) (singleton .overflowWrap) :=
  not_composable_of_hasAnyCollision_true
    (singleton .decimal) (singleton .overflowWrap) rfl

/-- L003: borrow x unscoped spawn is forbidden. -/
example :
    ¬ IsComposable (singleton .borrow) (singleton .unscopedSpawn) :=
  not_composable_of_hasAnyCollision_true
    (singleton .borrow) (singleton .unscopedSpawn) rfl

/-- M011 reduction guard: linear x Fail needs cleanup. -/
example :
    ¬ IsComposable (singleton .linear) (singleton .fail) :=
  not_composable_of_hasAnyCollision_true
    (singleton .linear) (singleton .fail) rfl

/-- S010: positive staleness x constant-time is forbidden. -/
example :
    ¬ IsComposable (singleton .stalenessPositive) (singleton .constantTime) :=
  not_composable_of_hasAnyCollision_true
    (singleton .stalenessPositive) (singleton .constantTime) rfl

/-- S011: capability x replay is forbidden unless a later grade proves
replay-stability. -/
example :
    ¬ IsComposable (singleton .capability) (singleton .replay) :=
  not_composable_of_hasAnyCollision_true
    (singleton .capability) (singleton .replay) rfl

end FxCollisionTrace

end LeanFX.Mode
