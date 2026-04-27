import FX.Kernel.Grade.Tier

/-!
# Overflow (dimension 16) — arithmetic overflow discipline

Per `fx_design.md` §6.3 (dim 16) and §3.1.  Four-element set
with **partial** order:

              wrap    trap    saturate
                \      |      /
                 \     |     /
                  \    |    /
                   exact

  * `exact`    — bottom; compiler must prove the result fits.
                 Default for arbitrary-precision types.
  * `wrap`     — two's-complement wraparound (C unsigned).
  * `trap`     — fault on overflow (Rust debug).
  * `saturate` — clamp to min/max (DSP).

## Surface-syntax mapping

Per `fx_design.md` §3.1, the source-level `with overflow(...)`
grants map one-to-one onto this carrier:

  * (no annotation)           → `exact`     (default for `int`/`nat`)
  * `with overflow(wrap)`     → `wrap`
  * `with overflow(trap)`     → `trap`
  * `with overflow(saturate)` → `saturate`

The default is the most restrictive setting (compiler must prove
the result fits the declared width); any of the other three
disciplines is an explicit grant from the programmer.

## Partial join — design-doc spec contradiction

§6.3 classifies Overflow as Tier S (semiring).  The spec then
says "mixing `wrap` and `trap` in the same expression is a type
error unless one is explicitly coerced".  A semiring requires
**total** `+` and `*`; an operation that errors on some inputs is
lattice-meet-with-validity, which is Tier L shape.

The kernel models this honestly: `add`/`mul` return `Option
Overflow`, with `none` representing the compile error.  When two
grades sit at the same element or along the `exact ≤ x` spine,
the join is defined; otherwise invalid.  The failure case is the
cross-discipline (top-vs-top) collision — `add wrap trap`,
`add wrap saturate`, `add trap saturate` and their duals all
return `none`.  This is the same validity-predicate shape that
Representation uses for `c ⊔ packed`; by convention the
corresponding diagnostic is the `T047`-class "incompatible
grade" error (Representation gets the name first in §8.5; the
Overflow spec gap — gaps.json — notes that this dimension
behaves Tier-L but is classified Tier-S in §6.3, leaving the
error code unnamed).

This diverges from §6.3's claim but matches the *behavior* the
spec describes.  Marking this inconsistency as a spec gap (it
belongs with the Tier-L dimensions alongside Representation and
Clock).
-/

namespace FX.Kernel

inductive Overflow : Type where
  | exact    : Overflow
  | wrap     : Overflow
  | trap     : Overflow
  | saturate : Overflow
  deriving DecidableEq, Repr

namespace Overflow

/--
Partial join: `exact` is the identity; the three tops join
with themselves idempotently; any two distinct tops collide
and return `none` (cross-discipline mixing is a compile error,
equivalent to the `T047` "incompatible grade" diagnostic the
Representation dimension surfaces for `c ⊔ packed`).
-/
def add : Overflow → Overflow → Option Overflow
  | exact,    rightOverflow => some rightOverflow
  | leftOverflow, exact     => some leftOverflow
  | wrap,     wrap     => some wrap
  | trap,     trap     => some trap
  | saturate, saturate => some saturate
  | _,        _        => none

/-- Sequential combine has the same shape. -/
def mul : Overflow → Overflow → Option Overflow := add

/-- Partial-order: `exact` is bottom; every element is `≤` itself. -/
inductive LessEq : Overflow → Overflow → Prop where
  | refl    : ∀ overflow, LessEq overflow overflow
  | exactLe : ∀ overflow, LessEq exact overflow

instance : LE Overflow := ⟨LessEq⟩

theorem LessEq.trans {lower middle upper : Overflow}
    (lowerMiddle : lower ≤ middle) (middleUpper : middle ≤ upper) : lower ≤ upper := by
  cases lowerMiddle with
  | refl    => exact middleUpper
  | exactLe =>
    cases middleUpper with
    | refl    => exact LessEq.exactLe _
    | exactLe => exact LessEq.exactLe _

instance decLe : (lower upper : Overflow) → Decidable (LessEq lower upper)
  | exact,    exact    => isTrue (LessEq.refl _)
  | exact,    wrap     => isTrue (LessEq.exactLe _)
  | exact,    trap     => isTrue (LessEq.exactLe _)
  | exact,    saturate => isTrue (LessEq.exactLe _)
  | wrap,     exact    => isFalse (fun relation => by cases relation)
  | wrap,     wrap     => isTrue (LessEq.refl _)
  | wrap,     trap     => isFalse (fun relation => by cases relation)
  | wrap,     saturate => isFalse (fun relation => by cases relation)
  | trap,     exact    => isFalse (fun relation => by cases relation)
  | trap,     wrap     => isFalse (fun relation => by cases relation)
  | trap,     trap     => isTrue (LessEq.refl _)
  | trap,     saturate => isFalse (fun relation => by cases relation)
  | saturate, exact    => isFalse (fun relation => by cases relation)
  | saturate, wrap     => isFalse (fun relation => by cases relation)
  | saturate, trap     => isFalse (fun relation => by cases relation)
  | saturate, saturate => isTrue (LessEq.refl _)

/--
Validity predicate for `add` — `true` iff the join is defined.
`¬ isAddDefined x y` corresponds to the `T047`-equivalent compile
error (cross-discipline overflow mixing).  Tracks the same
invariant shape as `Representation.isAddDefined`.
-/
def isAddDefined (leftOverflow rightOverflow : Overflow) : Prop :=
  (add leftOverflow rightOverflow).isSome

theorem add_comm (leftOverflow rightOverflow : Overflow) :
    add leftOverflow rightOverflow = add rightOverflow leftOverflow := by
  cases leftOverflow <;> cases rightOverflow <;> rfl

/-- Overflow mul is commutative.  `mul := add` by definition, so
    this is a direct re-export of `add_comm`.  Used by the aggregate
    `Grade.mul_comm_of_same_provenance` (Q48/T7). -/
theorem mul_comm (leftOverflow rightOverflow : Overflow) :
    mul leftOverflow rightOverflow = mul rightOverflow leftOverflow :=
  add_comm leftOverflow rightOverflow

theorem exact_add (overflow : Overflow) : add exact overflow = some overflow := by
  cases overflow <;> rfl

theorem add_exact (overflow : Overflow) : add overflow exact = some overflow := by
  cases overflow <;> rfl

/-- Idempotence on tops (the only non-bottom case where join is defined). -/
theorem add_idem (overflow : Overflow) : add overflow overflow = some overflow := by
  cases overflow <;> rfl

/--
Antisymmetry: `LessEq` is a genuine partial order on the four-element
carrier.  Follows directly from the two constructors — `refl`
leaves the element fixed, and `exactLe` can only go up from
`exact`, so the reverse direction must also be `exact`.
-/
theorem LessEq.antisymm {lower upper : Overflow}
    (lowerUpper : lower ≤ upper) (upperLower : upper ≤ lower) : lower = upper := by
  cases lowerUpper with
  | refl    => rfl
  | exactLe =>
    cases upperLower with
    | refl    => rfl
    | exactLe => rfl

/-- `exact` is the least element — every grade subsumes it from below. -/
theorem exact_le (overflow : Overflow) : exact ≤ overflow := LessEq.exactLe overflow

/--
The cross-discipline pairs: every mixing of two distinct
non-`exact` grades fails the validity predicate.  Surfaces as
the `T047`-equivalent compile error.
-/
theorem add_wrap_trap      : add wrap     trap     = none := rfl
theorem add_wrap_saturate  : add wrap     saturate = none := rfl
theorem add_trap_wrap      : add trap     wrap     = none := rfl
theorem add_trap_saturate  : add trap     saturate = none := rfl
theorem add_saturate_wrap  : add saturate wrap     = none := rfl
theorem add_saturate_trap  : add saturate trap     = none := rfl

end Overflow

/-! ## TierL instance (T4 — Overflow reclassified)

§6.3 classifies Overflow as Tier S, but its kernel — returning
`none` on cross-discipline mixing (`wrap + trap`, `wrap + saturate`,
`trap + saturate`) — is the Tier L validity-failure shape.  T6a
records this as a spec vs kernel mismatch to be resolved in Phase 2
(either the spec reclassifies Overflow to Tier L, or the kernel
adopts coercions that eliminate the `none` cases).  Until then, the
honest tier membership is `TierL`.

For `meetOpt` we reuse `add` since the operation is symmetric in
the Phase-1 carrier (no distinct "tighter" version of the
disciplines). -/
instance : TierL Overflow where
  default        := Overflow.exact
  le             := Overflow.LessEq
  le_refl        := Overflow.LessEq.refl
  le_trans       := Overflow.LessEq.trans
  joinOpt        := Overflow.add
  meetOpt        := Overflow.add
  joinOpt_comm   := Overflow.add_comm
  joinOpt_idem   := Overflow.add_idem
  meetOpt_comm   := Overflow.add_comm

end FX.Kernel
