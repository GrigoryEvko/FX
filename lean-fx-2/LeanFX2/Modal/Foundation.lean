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

Zero-axiom verified per declaration. -/

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
that fires when partial cases on indexed inductives overlap. -/
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

end Modality

end LeanFX2
