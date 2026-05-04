/-! # Action — Tier 3 Allais-style universal action typeclass.

The `Action` typeclass abstracts over data structures `Container : Nat
→ Nat → Type` that can be **lifted under binders** and **composed
sequentially**.  This is the foundational universe-of-syntax-with-
binding scaffold (Allais et al. ICFP'18, "A Type and Scope Safe Universe
of Syntaxes with Binding"), specialized for FX's raw-aware Term
architecture.

## Why an `Action` typeclass

Pre-Tier-3, every traversal-style operation (`Ty.weaken`, `Ty.rename`,
`Ty.subst`, `Ty.substHet`, `Term.weaken`, `Term.rename`, `Term.subst`,
`Term.substHet`, plus `RawTerm.{weaken,rename,subst}`) carries its own
recursion engine and its own ladder of commute lemmas:

* `Ty.rename_pointwise`, `Ty.subst_pointwise`, `Ty.substHet_pointwise`
* `Ty.rename_compose`, `Ty.subst_compose`, `Ty.subst_subst_compose`,
  `Ty.subst_substHet_compose`, `Ty.substHet_subst_compose`
* `Ty.weaken_rename_commute`, `Ty.weaken_subst_commute`,
  `Ty.weaken_substHet_commute`
* `Ty.subst0_rename_commute`, `Ty.subst0_subst_commute`,
  `Ty.subst0_substHet_commute`
* …mirrored at Term layer (3 copies) and RawTerm layer (~25 lemmas).

Per the MEGA-Z1.5 cast-and-commute map (`/tmp/mega-z1.5-comprehensive-
map.md`), this ladder totals **~174 propositional commute lemmas**
across 4 layers.  Most of them collapse under a unified `Action`
abstraction:

* `*_pointwise`        → `Action.apply_ext`         (extensionality)
* `*_compose`          → `Action.compose_assoc`     (associativity)
* `*_identity`         → `Action.identity_apply`    (identity law)
* `weaken_*_commute`   → `rfl` (weaken := identity-action.lift)
* `subst0_*_commute`   → `Action.compose_assoc`     (subst0 = singleton + compose)

## Dual-lift discipline (R11 — load-bearing)

`Ty.refine` carries `predicate : RawTerm (scope + 1)` — a RawTerm under
a binder, NOT a Ty under a binder.  Its `Ty.subst` arm uses
`sigma.forRaw.lift`, whereas `Ty.piTy`/`Ty.sigmaTy` use the unified
`sigma.lift`.

The `Action` typeclass therefore exposes **two lift methods**:
* `liftForTy`  — lift through a Ty-level binder (used by piTy/sigmaTy)
* `liftForRaw` — lift through a RawTerm-level binder (used by refine,
                  RawTerm.lam, RawTerm.pathLam)

For most concrete instances (`Subst`, `SubstHet`, `Renaming`) the two
lifts coincide structurally.  Keeping them as separate methods leaves
flexibility for instances where they MUST diverge (e.g., a `Renaming`
specialized to act only on raw indices).

## Pointwise laws (not raw equalities)

Function-typed Containers (`RawRenaming := Fin src → Fin tgt`) cannot
admit raw-equality laws zero-axiom (raw equalities of functions require
funext).  The typeclass therefore states its laws **pointwise** —
relative to a `headIndex` accessor that exposes the action's behaviour
at a single Fin position.  Concrete instances ship the headIndex
accessor and prove the pointwise laws via the underlying field-level
extensionality (Subst is a record, so record extensionality + per-field
pointwise laws suffice).

For Container types that ARE record-extensional (Subst, SubstHet),
the pointwise laws lift to data equalities via `Subst.ext`-style record
extensionality lemmas — those land in Z1.B.

## Identity action

`Action.identity` is the action that maps every variable to itself.
Instances must satisfy `compose identity x = x` and `compose x identity
= x` (pointwise, on the headIndex accessor).  For most instances these
are `rfl` after `simp only [identity, compose, headIndex]`.

## Layer

This file is at the **Foundation** layer — depends only on `Mathlib.Init`-
style Nat/Fin primitives and on `LeanFX2.Foundation.{Ty,RawTerm}` for
the `Ty` and `RawTerm` types that `ActionTarget` will instantiate.
However, the typeclass itself parameterises over `ActionTarget`, so it
does NOT pin to a specific `Ty`/`RawTerm` — it works for any
syntax-with-binding the project later defines.

## Audit

`Smoke/AuditMegaZ1A.lean` runs `#print axioms` on every declaration in
this file.  All zero-axiom under strict policy.

## Wave

Tier 3 / MEGA-Z1.A.  Z1.B wraps the existing `RawRenaming`, `Subst`,
`SubstHet` as instances.  Z2.A builds `Ty.act` over the Action
typeclass.  Z3 retires the propositional commute ladder.
-/

namespace LeanFX2

/-! ## Section 1 — The `Action` typeclass.

### Design rationale

`Container : Nat → Nat → Type` is a data-carrying transformer between
scopes.  An `Action` instance equips it with:
* `headIndex` — the variable case: what does the action do at a single
  Fin position of the source scope?  This is the "shape" of the action
  visible from outside the recursion.
* `liftForTy`, `liftForRaw` — extend the action under a Ty- or
  RawTerm-level binder.
* `identity` — the no-op action.
* `compose` — sequential composition of two actions.

The associated type `ActionTarget : Nat → Type` describes what
variables map to.  For renaming it's `Fin tgt`; for substitution it's
`Ty level tgt`; for substHet it's `Ty highLevel tgt`.

### Why `outParam`

`ActionTarget` is marked `outParam` so typeclass resolution can drive
target inference from the Container alone.  Concrete instances pin
`ActionTarget` to the right per-instance choice. -/

/-- Universal action typeclass.

`Container src tgt` is a data-carrying transformer between scopes.
An `Action` instance gives:
* `ActionTarget tgt` — what variables map to in the target scope
* `headIndex` — variable lookup in the source scope
* `liftForTy` / `liftForRaw` — extend under Ty- or RawTerm-level binder
* `identity` — no-op action
* `compose` — sequential composition

Laws are stated **pointwise** on `headIndex` to remain function-friendly
(no funext required).  Record-extensional instances (Subst, SubstHet)
will lift the pointwise laws to data equalities in Z1.B via record
extensionality. -/
class Action (Container : Nat → Nat → Type) where
  /-- The associated target type: what variables get mapped to. -/
  ActionTarget : outParam (Nat → Type)
  /-- Variable lookup at a single Fin position in the source scope. -/
  headIndex : ∀ {sourceScope targetScope : Nat},
      Container sourceScope targetScope →
      Fin sourceScope → ActionTarget targetScope
  /-- Lift through a Ty-level binder (piTy / sigmaTy codomain). -/
  liftForTy : ∀ {sourceScope targetScope : Nat},
      Container sourceScope targetScope →
      Container (sourceScope + 1) (targetScope + 1)
  /-- Lift through a RawTerm-level binder (refine / lam / pathLam). -/
  liftForRaw : ∀ {sourceScope targetScope : Nat},
      Container sourceScope targetScope →
      Container (sourceScope + 1) (targetScope + 1)
  /-- Identity action — variable maps to itself. -/
  identity : ∀ {scope : Nat}, Container scope scope
  /-- Sequential composition of two actions. -/
  compose : ∀ {sourceScope middleScope targetScope : Nat},
      Container sourceScope middleScope →
      Container middleScope targetScope →
      Container sourceScope targetScope
  /-- Pointwise headIndex accessor on `compose`: what does the composed
  action do at a single position?  Specified abstractly here as a
  proposition the instance must witness. -/
  composeAtHeadIndex : ∀ {sourceScope middleScope targetScope : Nat},
      Container sourceScope middleScope →
      Container middleScope targetScope →
      Fin sourceScope → ActionTarget targetScope
  /-- Composition associativity (pointwise). -/
  compose_assoc_pointwise : ∀ {sourceScope middleA middleB targetScope : Nat}
      (firstAction  : Container sourceScope middleA)
      (middleAction : Container middleA middleB)
      (lastAction   : Container middleB targetScope)
      (position : Fin sourceScope),
        composeAtHeadIndex (compose firstAction middleAction) lastAction position =
        composeAtHeadIndex firstAction (compose middleAction lastAction) position
  /-- Identity is a left-unit of compose (pointwise). -/
  compose_identity_left_pointwise : ∀ {sourceScope targetScope : Nat}
      (someAction : Container sourceScope targetScope)
      (position : Fin sourceScope),
        composeAtHeadIndex identity someAction position =
        headIndex someAction position
  /-- Identity is a right-unit of compose (pointwise). -/
  compose_identity_right_pointwise : ∀ {sourceScope targetScope : Nat}
      (someAction : Container sourceScope targetScope)
      (position : Fin sourceScope),
        composeAtHeadIndex someAction identity position =
        headIndex someAction position
  /-- `headIndex` of a `compose` agrees with the abstract
  `composeAtHeadIndex` field. -/
  headIndex_compose : ∀ {sourceScope middleScope targetScope : Nat}
      (firstAction  : Container sourceScope middleScope)
      (secondAction : Container middleScope targetScope)
      (position : Fin sourceScope),
        headIndex (compose firstAction secondAction) position =
        composeAtHeadIndex firstAction secondAction position

namespace Action

/-! ## Section 2 — Derived facts.

Pointwise laws on Container values, derived from the typeclass fields.
These are the consumer-facing names that recursion engines (Ty.act,
RawTerm.act, Term.act in Z2.A / Z4.A / Z5.A) will use. -/

variable {Container : Nat → Nat → Type} [Action Container]

/-- Composition is associative (pointwise on headIndex of the result). -/
theorem compose_assoc
    {sourceScope middleA middleB targetScope : Nat}
    (firstAction  : Container sourceScope middleA)
    (middleAction : Container middleA middleB)
    (lastAction   : Container middleB targetScope) :
    ∀ (position : Fin sourceScope),
      headIndex (compose (compose firstAction middleAction) lastAction) position =
      headIndex (compose firstAction (compose middleAction lastAction)) position := by
  intro position
  rw [headIndex_compose, headIndex_compose,
      compose_assoc_pointwise firstAction middleAction lastAction]

/-- Identity is a left unit of compose (pointwise). -/
theorem compose_identity_left
    {sourceScope targetScope : Nat}
    (someAction : Container sourceScope targetScope) :
    ∀ (position : Fin sourceScope),
      headIndex (compose identity someAction) position =
      headIndex someAction position := by
  intro position
  rw [headIndex_compose, compose_identity_left_pointwise someAction position]

/-- Identity is a right unit of compose (pointwise). -/
theorem compose_identity_right
    {sourceScope targetScope : Nat}
    (someAction : Container sourceScope targetScope) :
    ∀ (position : Fin sourceScope),
      headIndex (compose someAction identity) position =
      headIndex someAction position := by
  intro position
  rw [headIndex_compose, compose_identity_right_pointwise someAction position]

end Action

/-! ## Section 3 — The trivial identity instance (`IdAction`).

A smoke-test instance: `IdAction scope scope` is propositionally a
single inhabitant per scope (the identity action), and `IdAction
sourceScope targetScope` for `sourceScope ≠ targetScope` is an
empty type.  This demonstrates that the typeclass design is
inhabitable.

We use a `structure` (rather than `inductive`) because the structure
form generates only-rfl equation lemmas — no propext leak via match
arity (per `feedback_lean_match_arity_axioms.md`). -/

/-- Trivial identity Container.  `IdAction scope scope` carries no
data; `IdAction sourceScope targetScope` for `sourceScope ≠
targetScope` is uninhabited via the `dummyEqual` field (which forces
`sourceScope = targetScope`).

We ship this as a smoke-test instance to demonstrate the typeclass
design is inhabitable.  It is NOT used by any consumer — Z1.B's real
instances (Renaming, Subst, SubstHet) supplant it.

Note that `IdAction sourceScope targetScope` IS inhabited only when
`sourceScope = targetScope`, witnessed by `IdAction.identity`.  We
forward all dual-lift / compose operations to the obvious shape. -/
structure IdAction (sourceScope targetScope : Nat) : Type where
  scopeEqual : sourceScope = targetScope

namespace IdAction

/-- The canonical identity inhabitant. -/
@[reducible] def identity {scope : Nat} : IdAction scope scope where
  scopeEqual := rfl

/-- Lift through a Ty-level binder.  Since IdAction carries only a
proof of scope-equality, lifting just adds `1` to both sides via
`Nat.succ` congruence. -/
@[reducible] def liftForTy {sourceScope targetScope : Nat}
    (someAction : IdAction sourceScope targetScope) :
    IdAction (sourceScope + 1) (targetScope + 1) where
  scopeEqual := by rw [someAction.scopeEqual]

/-- Lift through a RawTerm-level binder.  Same shape as `liftForTy`
for IdAction (where they coincide structurally). -/
@[reducible] def liftForRaw {sourceScope targetScope : Nat}
    (someAction : IdAction sourceScope targetScope) :
    IdAction (sourceScope + 1) (targetScope + 1) where
  scopeEqual := by rw [someAction.scopeEqual]

/-- Sequential composition: chain two scope-equality witnesses. -/
@[reducible] def compose {sourceScope middleScope targetScope : Nat}
    (firstAction  : IdAction sourceScope middleScope)
    (secondAction : IdAction middleScope targetScope) :
    IdAction sourceScope targetScope where
  scopeEqual := by rw [firstAction.scopeEqual, secondAction.scopeEqual]

/-- Variable lookup: cast the input position via the scope-equality
witness.  Returns a `Fin targetScope`. -/
@[reducible] def headIndex {sourceScope targetScope : Nat}
    (someAction : IdAction sourceScope targetScope)
    (position : Fin sourceScope) : Fin targetScope :=
  someAction.scopeEqual ▸ position

/-- Pointwise headIndex on a `compose`: chain through the middle
scope.  This is the abstract `composeAtHeadIndex` field. -/
@[reducible] def composeAtHeadIndex {sourceScope middleScope targetScope : Nat}
    (firstAction  : IdAction sourceScope middleScope)
    (secondAction : IdAction middleScope targetScope)
    (position : Fin sourceScope) : Fin targetScope :=
  headIndex secondAction (headIndex firstAction position)

end IdAction

/-- The trivial identity instance.  Smoke test for the typeclass
design — verifies that `liftForTy`, `liftForRaw`, `identity`, and
`compose` cohere with the laws zero-axiom.

Z1.B's real instances (`Renaming`, `Subst`, `SubstHet`) follow the
same shape but with non-trivial Container data. -/
instance : Action IdAction where
  ActionTarget       := Fin
  headIndex          := IdAction.headIndex
  liftForTy          := IdAction.liftForTy
  liftForRaw         := IdAction.liftForRaw
  identity           := IdAction.identity
  compose            := IdAction.compose
  composeAtHeadIndex := IdAction.composeAtHeadIndex
  compose_assoc_pointwise firstAction middleAction lastAction position := by
    -- Destructure scope equalities so the two `▸`-casts on each side
    -- become `rfl`-casts.  Once all three witnesses are `rfl`, both
    -- LHS and RHS reduce definitionally to `position`.
    cases firstAction.scopeEqual
    cases middleAction.scopeEqual
    cases lastAction.scopeEqual
    rfl
  compose_identity_left_pointwise someAction position := by
    cases someAction.scopeEqual
    rfl
  compose_identity_right_pointwise someAction position := by
    cases someAction.scopeEqual
    rfl
  headIndex_compose firstAction secondAction position := by
    cases firstAction.scopeEqual
    cases secondAction.scopeEqual
    rfl

/-! ## Section 4 — Smoke test: dual-lift on a 3-ctor mock Ty.

Per the MEGA-Z1.A risk register entry **R11**, the dual-lift design
must accommodate ctors whose binders bind a Ty (like piTy) versus
ctors whose binders bind a RawTerm (like refine's predicate).

This section ships a 3-ctor mock `MockTy` and verifies that the
typeclass `liftForTy` and `liftForRaw` both elaborate cleanly when
used inside a recursion engine.  This validates the design before
Z2.A applies the same pattern to the real `Ty` inductive (25 ctors). -/

/-- Mock 3-ctor type to smoke-test dual-lift.  Subset of FX's real
`Ty` covering the three binder shapes:
* `MockTy.unit` — leaf, no binder
* `MockTy.binderTy` — Ty under binder (mimics piTy/sigmaTy)
* `MockTy.binderRaw` — RawTerm under binder (mimics refine)

For the smoke test we model "RawTerm under binder" as just another
MockTy — the actual binder shape is exercised by passing
`liftForRaw` instead of `liftForTy` to the inner recursive call. -/
inductive MockTy : Nat → Type where
  | unit       {scope : Nat}                          : MockTy scope
  | binderTy   {scope : Nat} (under : MockTy (scope + 1)) : MockTy scope
  | binderRaw  {scope : Nat} (under : MockTy (scope + 1)) : MockTy scope

/-- Mock recursion engine using dual-lift.  Demonstrates that the
`Action` typeclass's `liftForTy` and `liftForRaw` methods both
elaborate cleanly when threaded through a recursive structure. -/
def MockTy.act {Container : Nat → Nat → Type} [Action Container]
    {sourceScope targetScope : Nat}
    (someType : MockTy sourceScope)
    (someAction : Container sourceScope targetScope) :
    MockTy targetScope :=
  match someType with
  | .unit            => .unit
  | .binderTy under  => .binderTy (under.act (Action.liftForTy someAction))
  | .binderRaw under => .binderRaw (under.act (Action.liftForRaw someAction))

/-- Smoke test: applying the IdAction's identity to MockTy.unit
returns MockTy.unit unchanged.  This verifies the typeclass instance
elaborates and reduces cleanly through the recursion engine. -/
theorem MockTy.act_identity_unit_smoke {scope : Nat} :
    (MockTy.unit (scope := scope)).act (IdAction.identity) = MockTy.unit := rfl

/-- Smoke test: applying IdAction's identity to MockTy.binderTy
returns the same MockTy.binderTy.  This exercises `liftForTy`. -/
theorem MockTy.act_identity_binderTy_smoke {scope : Nat}
    (under : MockTy (scope + 1)) :
    (MockTy.binderTy under).act (IdAction.identity) =
    MockTy.binderTy (under.act (Action.liftForTy IdAction.identity)) := rfl

/-- Smoke test: applying IdAction's identity to MockTy.binderRaw
returns the same MockTy.binderRaw.  This exercises `liftForRaw`. -/
theorem MockTy.act_identity_binderRaw_smoke {scope : Nat}
    (under : MockTy (scope + 1)) :
    (MockTy.binderRaw under).act (IdAction.identity) =
    MockTy.binderRaw (under.act (Action.liftForRaw IdAction.identity)) := rfl

end LeanFX2
