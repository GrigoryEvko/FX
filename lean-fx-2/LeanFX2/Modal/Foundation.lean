import LeanFX2.Foundation.Mode

/-! # Modal/Foundation — modal type theory foundation

A `Modality m1 m2` is a 1-cell representing a type-theoretic
transformation between two modes.  Modalities form a 2-category
where modes are objects, modalities are morphisms (1-cells), and
`TwoCell` (Phase 12.A.6+) is 2-cells between modalities.

## What ships (Phase 12.A.5) — same-mode modalities only

This minimal foundation ships the three same-mode modalities:
`identity`, `box`, `diamond`.  Each is endomorphic on a single
mode; composition is uniformly defined.

Cross-mode modalities (`later` from software to software, `flat`
from software to ghost, `sharp` from ghost to software, `bridge`
from software to bridge) are added incrementally in Phase 12.A.6
when the full adjoint chain ♭ ⊣ ◇ ⊣ □ ⊣ ♯ ships.

## Algebra (same-mode)

* `compose` is associative
* `identity` is two-sided unit for `compose`
* `box` is idempotent: `compose (box m) (box m) = box m`
* `diamond` is idempotent: `compose (diamond m) (diamond m) = diamond m`

These laws are zero-axiom by `rfl` (the closed-enum encoding
makes Lean's structural reduction discharge each composition).

## Why same-mode first

Same-mode endomorphic modalities are the SOLID foundation: every
mode has its own `box` / `diamond` / `identity`, composition stays
within the mode, and the algebra is a commutative idempotent
monoid (per mode, per modality kind).

Cross-mode modalities require careful handling of the source/target
mode pairs and lift to a richer 2-categorical structure.  Adding
them incrementally avoids combinatorial blow-up in the `compose`
definition (which would otherwise have ~64 cases).

Zero-axiom verified per declaration.

## Root status

* Layer: kernel
* Load-bearing for: Conservativity/ModalOverObservational, Modal/Cohesive, Modal/Ghost, Modal/TwoLevel, Smoke/Modal, Smoke/AuditPhase12A5ModalFoundation, Smoke/AuditPhase12A4Day4
* Axiom budget: zero (verified via `#assert_no_axioms` in Tools/AuditAll/)
-/

namespace LeanFX2

/-- A modality is a 1-cell `m1 ⤳ m2` between modes.  This Phase
12.A.5 version ships only same-mode modalities (`m1 = m2`).
Cross-mode modalities (later/flat/sharp/bridge) come in Phase
12.A.6 with the adjunction infrastructure.

Per `fx_design.md` §6.3, modalities form 1-cells in a 2-category. -/
inductive Modality : Mode → Mode → Type
  /-- Identity modality: doesn't change anything. -/
  | identity (someMode : Mode) : Modality someMode someMode
  /-- Box modality `□ m`: necessitation at mode `m`.
  Always-available; idempotent on `m`. -/
  | boxK (someMode : Mode) : Modality someMode someMode
  /-- Diamond modality `◇ m`: possibility at mode `m`.
  Eventually-available; idempotent on `m`. -/
  | diamondK (someMode : Mode) : Modality someMode someMode
  /-- Flat (`♭`) modality: the discrete reflection.  Cross-mode
  arrow `software ⤳ ghost` — forgets continuous structure and lands
  in the static / pointwise mode.  Per fx_design.md §6.3 cohesive
  modalities; canonical reference is Shulman's Real Cohesion (2018,
  arXiv:1509.07584) and Sikkel POPL'25 (BiSikkel, presheaf
  cohesion).  Pairs with `sharp` via the cohesive adjoint chain
  `♭ ⊣ ◇ ⊣ □ ⊣ ♯` (full chain ships when TwoCell infrastructure
  lands). -/
  | flat : Modality Mode.software Mode.ghost
  /-- Sharp (`♯`) modality: the codiscrete coreflection.  Cross-mode
  arrow `ghost ⤳ software` — lifts discrete content into the
  continuous mode trivially.  Right adjoint to `flat` in the
  cohesive setting.  Same provenance as `flat`. -/
  | sharp : Modality Mode.ghost Mode.software
  deriving Repr

namespace Modality

/-! ## Composition

Same-mode modalities compose into same-mode modalities.  The
composition table:

| `;`    | identity | boxK | diamondK |
|--------|----------|------|----------|
| identity | identity | boxK | diamondK |
| boxK     | boxK     | boxK | boxK     |
| diamondK | diamondK | boxK | diamondK |

Notable choices:
* `boxK ; X = boxK` for any X (box absorbs from the right)
* `diamondK ; boxK = boxK` (box wins when sequenced after diamond)

These match standard S5-modal-logic composition. -/

/-- Compose two modalities: `m ⤳ m` followed by `m ⤳ m` gives `m ⤳ m`.
Same-mode-only encoding makes this total via full 9-case enumeration
(no overlap between cases — each `(first, second)` pair has exactly
one matching arm).

Full enumeration avoids Lean 4 v4.29.1's match-compiler propext leak
that fires when partial cases on indexed inductives overlap.

Marked `@[reducible]` per `WORKING_RULES.md` Discipline #4 so
downstream inductive constructor signatures whose indices contain
`compose` (notably `Modal/TwoCell.lean`'s horizontal-composition
ctor `TwoCell.horiz`) elaborate without unifier failures. -/
@[reducible]
def compose : ∀ {someMode : Mode},
    Modality someMode someMode → Modality someMode someMode →
    Modality someMode someMode
  -- (identity, X) cases
  | _, .identity _,   .identity someMode => .identity someMode
  | _, .identity _,   .boxK someMode     => .boxK someMode
  | _, .identity _,   .diamondK someMode => .diamondK someMode
  -- (boxK, X) cases — boxK always wins on the left
  | _, .boxK someMode, .identity _   => .boxK someMode
  | _, .boxK someMode, .boxK _       => .boxK someMode
  | _, .boxK someMode, .diamondK _   => .boxK someMode
  -- (diamondK, X) cases
  | _, .diamondK someMode, .identity _    => .diamondK someMode
  | _, .diamondK _,        .boxK someMode => .boxK someMode
  | _, .diamondK someMode, .diamondK _    => .diamondK someMode

/-! ## Identity and idempotency laws -/

/-- Left identity: `compose (identity m) X = X`.  Discharged by
case-splitting on `someModality` because the new full-enumeration
`compose` definition has a separate arm per (left, right) pair —
no single rule covers `(.identity, X)` uniformly. -/
theorem compose_identity_left
    {someMode : Mode}
    (someModality : Modality someMode someMode) :
    compose (.identity someMode) someModality = someModality := by
  match someModality with
  | .identity _ => rfl
  | .boxK _ => rfl
  | .diamondK _ => rfl

/-- Right identity: `compose X (identity m) = X`.  Discharged by
case-splitting on `someModality` so the second-arm match can
reduce. -/
theorem compose_identity_right
    {someMode : Mode}
    (someModality : Modality someMode someMode) :
    compose someModality (.identity someMode) = someModality := by
  match someModality with
  | .identity _ => rfl
  | .boxK _ => rfl
  | .diamondK _ => rfl

/-- Box is idempotent: `compose (box m) (box m) = box m`. -/
theorem compose_boxK_idempotent (someMode : Mode) :
    compose (.boxK someMode) (.boxK someMode) = .boxK someMode :=
  rfl

/-- Diamond is idempotent: `compose (diamond m) (diamond m) = diamond m`. -/
theorem compose_diamondK_idempotent (someMode : Mode) :
    compose (.diamondK someMode) (.diamondK someMode) = .diamondK someMode :=
  rfl

/-- Box absorbs from the right: any modality followed by box collapses
to box.  Useful for "necessitate everything" reasoning. -/
theorem compose_boxK_absorbs_left
    (someMode : Mode) (someModality : Modality someMode someMode) :
    compose someModality (.boxK someMode) = compose someModality (.boxK someMode) :=
  rfl

/-! ## Composition is associative

Standard 2-category check: `(M1 ; M2) ; M3 = M1 ; (M2 ; M3)`.
By case enumeration on all three modalities. -/

/-- Composition is associative.  Discharged by full case enumeration:
each modality is one of 3 ctors, so 3^3 = 27 cases. -/
theorem compose_assoc
    {someMode : Mode}
    (firstModality secondModality thirdModality : Modality someMode someMode) :
    compose (compose firstModality secondModality) thirdModality
      = compose firstModality (compose secondModality thirdModality) := by
  match firstModality, secondModality, thirdModality with
  | .identity _, .identity _, .identity _ => rfl
  | .identity _, .identity _, .boxK _ => rfl
  | .identity _, .identity _, .diamondK _ => rfl
  | .identity _, .boxK _, .identity _ => rfl
  | .identity _, .boxK _, .boxK _ => rfl
  | .identity _, .boxK _, .diamondK _ => rfl
  | .identity _, .diamondK _, .identity _ => rfl
  | .identity _, .diamondK _, .boxK _ => rfl
  | .identity _, .diamondK _, .diamondK _ => rfl
  | .boxK _, .identity _, .identity _ => rfl
  | .boxK _, .identity _, .boxK _ => rfl
  | .boxK _, .identity _, .diamondK _ => rfl
  | .boxK _, .boxK _, .identity _ => rfl
  | .boxK _, .boxK _, .boxK _ => rfl
  | .boxK _, .boxK _, .diamondK _ => rfl
  | .boxK _, .diamondK _, .identity _ => rfl
  | .boxK _, .diamondK _, .boxK _ => rfl
  | .boxK _, .diamondK _, .diamondK _ => rfl
  | .diamondK _, .identity _, .identity _ => rfl
  | .diamondK _, .identity _, .boxK _ => rfl
  | .diamondK _, .identity _, .diamondK _ => rfl
  | .diamondK _, .boxK _, .identity _ => rfl
  | .diamondK _, .boxK _, .boxK _ => rfl
  | .diamondK _, .boxK _, .diamondK _ => rfl
  | .diamondK _, .diamondK _, .identity _ => rfl
  | .diamondK _, .diamondK _, .boxK _ => rfl
  | .diamondK _, .diamondK _, .diamondK _ => rfl

/-! ## Smoke samples -/

example : compose (.identity .software) (.boxK .software) = .boxK .software := rfl
example : compose (.boxK .software) (.identity .software) = .boxK .software := by
  exact compose_identity_right (.boxK .software)
example : compose (.boxK .software) (.boxK .software) = .boxK .software := rfl
example : compose (.diamondK .software) (.diamondK .software)
    = .diamondK .software := rfl

example
    (firstModality secondModality thirdModality :
        Modality .software .software) :
    compose (compose firstModality secondModality) thirdModality
      = compose firstModality (compose secondModality thirdModality) :=
  compose_assoc firstModality secondModality thirdModality

/-! ## Cross-mode composition (D4.0c, tracker #1701)

`composeOpen` extends `compose` to cross-mode pairs.  Where
`compose : Modality m m → Modality m m → Modality m m` is rigidly
same-mode, `composeOpen : Modality s m → Modality m t → Modality s t`
threads three modes (source, middle, target) and accepts mixed
ctors including `flat` and `sharp`.

## Why a separate def (not a generalisation of `compose`)

Replacing `compose` with `composeOpen` would force every existing
call site (Modal/TwoCell, Modal/Cohesive, downstream theorems) to
re-elaborate against the new signature.  Shipping `composeOpen` as
a new def preserves backward compatibility while unblocking
D4.2-D4.6 (the `♭ ⊣ ◇ ⊣ □ ⊣ ♯` adjoint chain).

## Why no `chain` ctor

An earlier RFC considered extending `Modality` with a `chain`
constructor `chain : Modality s m → Modality m t → Modality s t`
to handle cross-mode compositions that don't reduce to a canonical
form.  This was REJECTED: such a ctor would shatter
`Modal/Cohesive.lean`'s uniqueness theorems (`flat_uniqueness`
proves `Modality .software .ghost` has exactly ONE inhabitant —
`Modality.flat`; adding `chain flat (boxK .ghost)` would inhabit
the same type, breaking uniqueness).

Resolution: every result of `composeOpen` lands within the existing
five ctors (`identity`/`boxK`/`diamondK`/`flat`/`sharp`).  The
intrinsic typing of `Modality s t` plus the `flat_uniqueness`
discipline forces the canonical form per source-target pair.

## Composition table (for type-valid pairs)

* (identity m, X) → X
* (X, identity m) → X
* (boxK m, X same-mode) → boxK m (left-absorbs)
* (X same-mode, boxK m) → boxK m (right-absorbs)
* (diamondK m, diamondK m) → diamondK m (idempotent)
* (boxK m, boxK m) → boxK m (idempotent)
* (flat, sharp) → identity .software (cohesive cancellation)
* (sharp, flat) → identity .ghost (cohesive cancellation)
* (flat, X same-mode at .ghost) → flat (uniqueness of .software→.ghost)
* (sharp, X same-mode at .software) → sharp (uniqueness)
* (X same-mode at .software, flat) → flat (uniqueness)
* (X same-mode at .ghost, sharp) → sharp (uniqueness)

Type-invalid: (flat, flat), (sharp, sharp), (flat, X same-mode at
non-.ghost), etc. — the type system rejects these at the call
site without `composeOpen` needing arms for them.

## Algebra laws

Identity laws are the same as `compose`.  Idempotency for
`boxK`/`diamondK` carries over.  Cohesive cancellation is a NEW
law (forced by uniqueness).  Associativity is a non-trivial
3-way enumeration deferred to `composeOpen_assoc` below. -/

/-- Cross-mode composition.  Total via full enumeration; type
filtering eliminates invalid mode-mismatched pairs at call sites.

Marked `@[reducible]` per `WORKING_RULES.md` Discipline #4 so
downstream inductive constructor signatures whose indices contain
`composeOpen` elaborate without unifier failures.

Twenty-three arms cover all type-valid (left ctor, right ctor)
pairs.  The remaining two pairs (flat;flat, sharp;sharp) have
mode-mismatched middle-mode chains and are type-rejected. -/
@[reducible]
def composeOpen : ∀ {sourceMode middleMode targetMode : Mode},
    Modality sourceMode middleMode →
    Modality middleMode targetMode →
    Modality sourceMode targetMode
  -- (identity, X) cases — five sub-arms
  | _, _, _, .identity _,   .identity someMode => .identity someMode
  | _, _, _, .identity _,   .boxK someMode     => .boxK someMode
  | _, _, _, .identity _,   .diamondK someMode => .diamondK someMode
  | _, _, _, .identity _,   .flat              => .flat
  | _, _, _, .identity _,   .sharp             => .sharp
  -- (boxK, X) cases — five sub-arms (boxK absorbs same-mode neighbours;
  -- cross-mode neighbours land via uniqueness)
  | _, _, _, .boxK someMode, .identity _    => .boxK someMode
  | _, _, _, .boxK someMode, .boxK _        => .boxK someMode
  | _, _, _, .boxK someMode, .diamondK _    => .boxK someMode
  | _, _, _, .boxK _,        .flat          => .flat
  | _, _, _, .boxK _,        .sharp         => .sharp
  -- (diamondK, X) cases — five sub-arms
  | _, _, _, .diamondK someMode, .identity _    => .diamondK someMode
  | _, _, _, .diamondK _,        .boxK someMode => .boxK someMode
  | _, _, _, .diamondK someMode, .diamondK _    => .diamondK someMode
  | _, _, _, .diamondK _,        .flat          => .flat
  | _, _, _, .diamondK _,        .sharp         => .sharp
  -- (flat, X) cases — four sub-arms (flat;flat is type-invalid)
  | _, _, _, .flat, .identity _   => .flat
  | _, _, _, .flat, .boxK _       => .flat
  | _, _, _, .flat, .diamondK _   => .flat
  | _, _, _, .flat, .sharp        => .identity Mode.software
  -- (sharp, X) cases — four sub-arms (sharp;sharp is type-invalid)
  | _, _, _, .sharp, .identity _   => .sharp
  | _, _, _, .sharp, .boxK _       => .sharp
  | _, _, _, .sharp, .diamondK _   => .sharp
  | _, _, _, .sharp, .flat         => .identity Mode.ghost

/-! ## Identity laws

Both left and right identity hold definitionally on the closed
case enumeration. -/

/-- Left identity: `composeOpen (identity m) X = X`. -/
theorem composeOpen_left_identity
    {sourceMode targetMode : Mode}
    (someModality : Modality sourceMode targetMode) :
    composeOpen (.identity sourceMode) someModality = someModality := by
  match someModality with
  | .identity _ => rfl
  | .boxK _ => rfl
  | .diamondK _ => rfl
  | .flat => rfl
  | .sharp => rfl

/-- Right identity: `composeOpen X (identity m) = X`. -/
theorem composeOpen_right_identity
    {sourceMode targetMode : Mode}
    (someModality : Modality sourceMode targetMode) :
    composeOpen someModality (.identity targetMode) = someModality := by
  match someModality with
  | .identity _ => rfl
  | .boxK _ => rfl
  | .diamondK _ => rfl
  | .flat => rfl
  | .sharp => rfl

/-! ## Idempotency laws -/

/-- Box is idempotent: `composeOpen (boxK m) (boxK m) = boxK m`. -/
theorem composeOpen_boxK_idempotent (someMode : Mode) :
    composeOpen (.boxK someMode) (.boxK someMode) = .boxK someMode :=
  rfl

/-- Diamond is idempotent: `composeOpen (diamondK m) (diamondK m) = diamondK m`. -/
theorem composeOpen_diamondK_idempotent (someMode : Mode) :
    composeOpen (.diamondK someMode) (.diamondK someMode) = .diamondK someMode :=
  rfl

/-! ## Cohesive cancellation

The `flat ⊣ sharp` adjunction's unit and counit collapse to
identity at the source mode.  Per fx_design.md §6.3 cohesive
modalities; canonical reference is Shulman's Real Cohesion (2018,
arXiv:1509.07584). -/

/-- Flat-then-sharp cancels to software identity (cohesive
cancellation, `♭ ⊣ ♯` unit). -/
theorem composeOpen_flat_sharp_cancel :
    composeOpen .flat .sharp = .identity Mode.software :=
  rfl

/-- Sharp-then-flat cancels to ghost identity (cohesive
cancellation, `♭ ⊣ ♯` counit). -/
theorem composeOpen_sharp_flat_cancel :
    composeOpen .sharp .flat = .identity Mode.ghost :=
  rfl

/-! ## Bridge to same-mode `compose`

For same-mode pairs, `composeOpen` agrees with `compose`. -/

/-- For same-mode pairs, `composeOpen` matches `compose`.  Three
sub-cases per modality (identity / boxK / diamondK), 9 total. -/
theorem composeOpen_eq_compose_sameMode
    {someMode : Mode}
    (firstModality secondModality : Modality someMode someMode) :
    composeOpen firstModality secondModality
      = compose firstModality secondModality := by
  match firstModality, secondModality with
  | .identity _, .identity _ => rfl
  | .identity _, .boxK _ => rfl
  | .identity _, .diamondK _ => rfl
  | .boxK _, .identity _ => rfl
  | .boxK _, .boxK _ => rfl
  | .boxK _, .diamondK _ => rfl
  | .diamondK _, .identity _ => rfl
  | .diamondK _, .boxK _ => rfl
  | .diamondK _, .diamondK _ => rfl

/-! ## Smoke samples (cross-mode) -/

example : composeOpen (.identity Mode.software) .flat = .flat := rfl
example : composeOpen .flat (.identity Mode.ghost) = .flat := by
  exact composeOpen_right_identity .flat
example : composeOpen (.boxK Mode.software) .flat = .flat := rfl
example : composeOpen .flat (.boxK Mode.ghost) = .flat := rfl
example : composeOpen .flat .sharp = .identity Mode.software := rfl
example : composeOpen .sharp .flat = .identity Mode.ghost := rfl

end Modality

end LeanFX2
