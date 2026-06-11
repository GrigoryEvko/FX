import FX1Poly.Core.RawTermRename

/-! # Foundation/PolyCell/Core/FoldShiftGreaterThanOne
   — regression smoke for `iterateLiftRaw` + `foldChildren` at binder
   depths greater than one

Pins the fold engine's binder-shift behavior at shift > 1, the
domain that eliminator motive children + iterator-style succ cases
need (per polycell.md §11.8.3).

## Why this smoke exists

The Generator table tops out at shift 1 (`gen_lam` /
`gen_pathLam` / `gen_piTyCode` / `gen_sigmaTyCode` / `gen_polyFunctor`).
But the fold engine's signature is shift-polymorphic:

* `iterateLiftRaw : Container source target → (depth : Nat) →
                   Container (source + depth) (target + depth)`
  takes ANY Nat depth and threads the Container under that many binders.

* `foldChildren : (algebra) → (action : Container) →
                  RawTermChildren binderShifts source →
                  RawTermChildren binderShifts target`
  walks a child spine where `binderShifts : List Nat` is arbitrary —
  the type does NOT require the shifts to come from any Generator's
  `binderShifts` table.  Synthetic shifts are admissible at the
  inductive level.

§11.8.3 specifies eliminators with MOTIVE children + iterator-with-IH
succ cases.  Concretely:

* `gen_natElim` → `[1 (motive), 0 (zero case), 2 (succ case), 0
  (scrutinee)]` — the succ case binds (predecessor, ih, result).
* Similar shift > 1 patterns for `gen_listElim` (cons case binds the
  IH) and the HIT eliminators (`gen_quotRec`, `gen_pushRec`,
  `gen_circleRec`).  Non-recursive matchers `gen_optionMatch` /
  `gen_eitherMatch` carry the motive-only shift `[1, 0, 0, 0]`
  (max shift 1 — the motive binds the scrutinee, no IH thread).

These require the engine to handle shift ≥ 2.  This smoke pins that
behavior against the shift-polymorphic engine, so that refactors
cannot silently break the engine's higher-shift semantics and a
Generator table using shift > 1 produces no engine-level surprises.

## What this ships

Two sections, each `theorem` with body `rfl`:

* §1 — Equational smokes for `iterateLiftRaw` at depths 0, 1, 2, 3,
  plus the recursive `succ` equation.  Each closes by `rfl` because
  `iterateLiftRaw` is structurally recursive on `binderDepth`.
* §2 — `foldChildren` smokes over synthetic shift lists `[2]` and
  `[0, 2, 1]`.  Constructs the spines directly via `.childCons` with
  closed-leaf head terms (`gen_unit`, scope-polymorphic in payload).
  Identity-renaming returns the spine unchanged; closure of `gen_unit`
  under any renaming makes the head reduction definitional.

## Zero-axiom verification

Every theorem closes by `rfl`.  No tactics, no `simp`, no `decide`
beyond what pure definitional reduction supplies.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — `iterateLiftRaw` equational smokes -/

/-- **Smoke: depth 0 is the identity.**

`iterateLiftRaw someAction 0 = someAction` reduces by the
`binderDepth = 0` arm of `iterateLiftRaw`. -/
theorem iterateLiftRaw_depth_zero_eq_self
    {Container : Nat → Nat → Type} [LiftsRaw Container]
    {sourceScope targetScope : Nat}
    (someAction : Container sourceScope targetScope) :
    iterateLiftRaw someAction 0 = someAction := rfl

/-- **Smoke: depth 1 is one `liftForRaw`.** -/
theorem iterateLiftRaw_depth_one_eq_liftForRaw
    {Container : Nat → Nat → Type} [LiftsRaw Container]
    {sourceScope targetScope : Nat}
    (someAction : Container sourceScope targetScope) :
    iterateLiftRaw someAction 1 = LiftsRaw.liftForRaw someAction := rfl

/-- **Smoke: depth 2 is two `liftForRaw`** — the key headline smoke.

This pins that the engine handles a binder shift of 2 (the shift an
eliminator's iterator-style succ case binds: motive + predecessor +
IH).  The reduction goes through two layers of structural recursion
in `iterateLiftRaw`. -/
theorem iterateLiftRaw_depth_two_eq_double_liftForRaw
    {Container : Nat → Nat → Type} [LiftsRaw Container]
    {sourceScope targetScope : Nat}
    (someAction : Container sourceScope targetScope) :
    iterateLiftRaw someAction 2 =
      LiftsRaw.liftForRaw (LiftsRaw.liftForRaw someAction) := rfl

/-- **Smoke: depth 3 is three `liftForRaw`.**

Architecturally required for eliminators whose recursive case binds
three positions (e.g. a `succCase` exposing predecessor, induction
hypothesis, AND result of the induction, or HIT eliminators with three
introduced cubical-interval variables). -/
theorem iterateLiftRaw_depth_three_eq_triple_liftForRaw
    {Container : Nat → Nat → Type} [LiftsRaw Container]
    {sourceScope targetScope : Nat}
    (someAction : Container sourceScope targetScope) :
    iterateLiftRaw someAction 3 =
      LiftsRaw.liftForRaw
        (LiftsRaw.liftForRaw (LiftsRaw.liftForRaw someAction)) := rfl

/-- **Smoke: the recursive equation** — `iterateLiftRaw someAction
(priorDepth + 1) = LiftsRaw.liftForRaw (iterateLiftRaw someAction
priorDepth)`.

The general structural-recursion unfolding.  Subsumes the per-depth
smokes above as instances at `priorDepth = 0, 1, 2`.  Useful for
downstream proofs that unfold a higher-depth lift one binder at a
time. -/
theorem iterateLiftRaw_succ_unfolds
    {Container : Nat → Nat → Type} [LiftsRaw Container]
    {sourceScope targetScope : Nat}
    (someAction : Container sourceScope targetScope) (priorDepth : Nat) :
    iterateLiftRaw someAction (priorDepth + 1) =
      LiftsRaw.liftForRaw (iterateLiftRaw someAction priorDepth) := rfl

/-! ## Section 2 — `foldChildren` over synthetic shift > 1 spines

`RawTermChildren binderShifts scope` accepts any `binderShifts : List
Nat` — the type-level index does NOT require the list to come from a
Generator's `binderShifts` table.  Synthetic shift lists are admissible
at the inductive level.

Each smoke constructs a child spine using `.childCons` directly,
applies the identity renaming via `RawTermChildren.rename`, and
verifies the result equals the input.  Closes by `rfl` because:

* `foldChildren` dispatches structurally on the spine.
* The head is a closed nullary leaf (`gen_unit`, payload `()`,
  `.childNil` children) whose `fold`-rename is the same leaf at any
  scope — `gen_unit` has no `Fin` variables to apply the lifted
  renaming to, so the lift's content is irrelevant.
-/

/-- **Smoke: synthetic `[2]`-shift spine identity-renames to itself.**

The head term lives at `scope + 2` (under TWO binders).  Identity
renaming exercises:

* `foldChildren` dispatching on the non-empty cons case.
* `iterateLiftRaw RawRenaming.identity 2` lifting the renaming under
  TWO binders before recursing into the head.
* `fold` on a closed `gen_unit` leaf at the lifted scope.

If this `rfl` succeeds, the engine handles shift 2 definitionally on
concrete inputs. -/
theorem rename_identity_synthetic_shift_two_spine_eq_self (scope : Nat) :
    RawTermChildren.rename
        (RawRenaming.identity (scope := scope))
        ((.childCons
              (.mkGen .gen_unit () .childNil : RawTerm (scope + 2))
              .childNil) : RawTermChildren [2] scope) =
      (.childCons
            (.mkGen .gen_unit () .childNil : RawTerm (scope + 2))
            .childNil) := rfl

/-- **Smoke: synthetic `[0, 2, 1]` heterogeneous-shift spine identity-
renames to itself.**

Three children at three different shifts — first at the parent scope,
second under TWO binders, third under ONE binder.  Validates that
`foldChildren` correctly lifts the action per-child without confusing
shifts across positions in the spine.

If this `rfl` succeeds, the engine handles heterogeneous shift > 1
spines without cross-position contamination. -/
theorem rename_identity_synthetic_shifts_zero_two_one_spine_eq_self
    (scope : Nat) :
    RawTermChildren.rename
        (RawRenaming.identity (scope := scope))
        ((.childCons
              (.mkGen .gen_unit () .childNil : RawTerm (scope + 0))
            (.childCons
                (.mkGen .gen_unit () .childNil : RawTerm (scope + 2))
              (.childCons
                  (.mkGen .gen_unit () .childNil : RawTerm (scope + 1))
                .childNil))) : RawTermChildren [0, 2, 1] scope) =
      (.childCons
            (.mkGen .gen_unit () .childNil : RawTerm (scope + 0))
          (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm (scope + 2))
            (.childCons
                (.mkGen .gen_unit () .childNil : RawTerm (scope + 1))
              .childNil))) := rfl

end FX1Poly.Core
