import FX.Kernel.Grade.Tier

/-!
# Representation (dimension 10) — memory layout attributes

Per `fx_design.md` §6.3 (dim 10) and §8.5.  Tier L (lattice
with validity predicate).  Axiom realized: `Grade-lattice`
(Appendix H.8) — "the grade set R_D forms a lattice (R_D, ∨, ∧)
with a validity predicate valid_D: R_D → bool.  At join/meet
sites, if valid_D(join(a, b)) = false, the expression is a
compile error (e.g., clock-domain mismatch CD001,
**representation incompatibility T047**)."

## Surface attributes (§8.5)

The design names six surface attributes:

  * `repr(Native)`      — compiler chooses (default).
  * `repr(C)`           — C ABI-compatible struct layout.
  * `repr(packed)`      — no padding between fields.
  * `repr(aligned(n))`  — `n`-byte alignment.
  * `repr(big_endian)`  — multi-byte fields big-endian.
  * `repr(transparent)` — same layout as the wrapped type.

## Phase-1 kernel carrier

This module ships four of the attributes plus a lattice-top
sentinel.  The two deferrals and the sentinel all have precise
reasons:

  * `native`     — `repr(Native)` in the surface.
  * `c`          — `repr(C)`.
  * `packed`     — `repr(packed)`.
  * `bigEndian`  — `repr(big_endian)`.
  * `noSpec`     — kernel-internal top-of-lattice sentinel.
                   Represents "no layout constraint beyond what
                   either operand imposed" after a join that
                   does not itself pick a concrete layout.
                   There is no surface `repr(noSpec)`;
                   elaboration never produces this value
                   directly, only the `add`/`mul` operations
                   reach it.  It materializes the algebraic
                   top so `LessEq` gets a non-trivial greatest
                   element and the lattice laws hold without
                   resorting to `Option Representation`
                   everywhere.
  * `repr(aligned(n))`  — **deferred**.  Requires a parametric
                   carrier (`aligned : Nat → Representation`);
                   this would force either opening `Nat` into
                   the inductive (complicating decidable
                   equality and finite-window test harnesses)
                   or a separate parameterized lattice that we
                   compose with this one.  Phase 2 choice.
  * `repr(transparent)` — **deferred**.  The wrapping is a
                   reference to the wrapped type — a type-level
                   dependency the kernel grade layer does not
                   carry.  Handled at elaboration time by
                   inlining the wrapped type's representation
                   grade; no carrier entry needed here once the
                   elaborator is in place.

## Partial join `add`

Per the design, `add` = coarsest compatible layout.  The
validity failure case (`add a b = none`) is compile error
`T047` (incompatible representation).  In the Phase-1 carrier:

  * `c ⊔ packed`  — **invalid**.  `repr(C)` implies ABI
                    padding; `repr(packed)` forbids padding.
                    No layout satisfies both — `T047`.
  * All other pairs are compatible: `native` is the bottom
    identity, `noSpec` is the top, `bigEndian` is layout-
    independent so it pairs with `c` or `packed`, and
    idempotent diagonal cases return themselves.

## Partial meet `meet`

The design explicitly states "**meet** = tightest compatible
layout".  We expose `meet` as the dual of `add`:

  * `c ⊓ packed` — still invalid (`T047`): same incompatibility
                   as the join direction, just from the other
                   side.
  * `noSpec ⊓ x = x` — `noSpec` is the top; meeting with it
                       returns the other operand.
  * `native ⊓ x = native` — `native` is the bottom; meeting
                            with it returns the bottom.
  * Idempotent diagonals, `bigEndian` independence as for `add`.

## Subsumption `LessEq`

Reflexive + `native ≤ x` (bottom) + `x ≤ noSpec` (top).  This
is the minimal preorder captured by the inductive; the
`isAddDefined`-respecting partial cases (e.g., `c ≤ noSpec` via
transitivity through a concrete path) are all derivable.
-/

namespace FX.Kernel

inductive Representation : Type where
  | native    : Representation
  | cCompat   : Representation
  | packed    : Representation
  | bigEndian : Representation
  | noSpec    : Representation
  deriving DecidableEq, Repr

namespace Representation

/--
Partial **join** (coarsest compatible layout).  Returns `none`
when the two constraints are incompatible — T047 in the §10.10
error taxonomy.
-/
def add : Representation → Representation → Option Representation
  -- noSpec is the top: anything joined with noSpec is noSpec.
  | noSpec,    _        => some noSpec
  | _,         noSpec   => some noSpec
  -- native is the bottom identity.
  | native,    rightRep => some rightRep
  | leftRep,   native   => some leftRep
  -- idempotent diagonal cases.
  | cCompat,   cCompat   => some cCompat
  | packed,    packed   => some packed
  | bigEndian, bigEndian=> some bigEndian
  -- bigEndian is independent of layout — compatible with c/packed.
  | cCompat,   bigEndian=> some cCompat
  | bigEndian, cCompat   => some cCompat
  | packed,    bigEndian=> some packed
  | bigEndian, packed   => some packed
  -- c ⊔ packed is the one invalid pair — T047.
  | cCompat,   packed    => none
  | packed,    cCompat   => none

/-- Sequential combine — same join. -/
def mul : Representation → Representation → Option Representation := add

/--
Partial **meet** (tightest compatible layout).  Dual of `add`.
Same invalid pair (`c ⊓ packed`) — incompatibility is
symmetric across the lattice direction.

  * `noSpec` is the top: meeting with noSpec returns the other.
  * `native` is the bottom: meeting with native returns native.
  * idempotent diagonals.
  * `bigEndian` pairs with `c`/`packed` returning the layout
    partner (meet = keep the tighter constraint).
-/
def meet : Representation → Representation → Option Representation
  -- noSpec is the top: anything met with noSpec is the other operand.
  | noSpec,    rightRep => some rightRep
  | leftRep,   noSpec   => some leftRep
  -- native is the bottom: anything met with native is native.
  | native,    _        => some native
  | _,         native   => some native
  -- idempotent diagonals.
  | cCompat,   cCompat   => some cCompat
  | packed,    packed   => some packed
  | bigEndian, bigEndian=> some bigEndian
  -- bigEndian is layout-independent — the layout operand wins.
  | cCompat,   bigEndian=> some cCompat
  | bigEndian, cCompat   => some cCompat
  | packed,    bigEndian=> some packed
  | bigEndian, packed   => some packed
  -- c ⊓ packed is invalid — T047.
  | cCompat,   packed    => none
  | packed,    cCompat   => none

/-- Validity predicate for `add` — `true` iff the join is
    defined.  Failure corresponds to error code T047. -/
def isAddDefined (leftRep rightRep : Representation) : Prop := (add leftRep rightRep).isSome

/-- Validity predicate for `meet` — dual of `isAddDefined`. -/
def isMeetDefined (leftRep rightRep : Representation) : Prop := (meet leftRep rightRep).isSome

/--
Subsumption order.  `native` is the bottom (every layout
refines the compiler-chosen default), `noSpec` is the top (no
constraint).
-/
inductive LessEq : Representation → Representation → Prop where
  | refl        : ∀ representation, LessEq representation representation
  | nativeLe    : ∀ representation, LessEq native representation
  | leNoSpec    : ∀ representation, LessEq representation noSpec

instance : LE Representation := ⟨LessEq⟩

theorem LessEq.trans {leftRep midRep rightRep : Representation}
    (hLeftMid : leftRep ≤ midRep) (hMidRight : midRep ≤ rightRep) :
    leftRep ≤ rightRep := by
  cases hLeftMid with
  | refl     => exact hMidRight
  | nativeLe =>
    cases hMidRight with
    | refl     => exact LessEq.nativeLe _
    | nativeLe => exact LessEq.nativeLe _
    | leNoSpec => exact LessEq.nativeLe _
  | leNoSpec =>
    cases hMidRight with
    | refl     => exact LessEq.leNoSpec _
    | leNoSpec => exact LessEq.leNoSpec _

/--
Decidability of `LessEq`.  `LessEq x y` holds iff `x = y`, `x = native`,
or `y = noSpec`.  All three are discriminable by pattern
matching on both operands.
-/
instance decLe : (leftRep rightRep : Representation) → Decidable (LessEq leftRep rightRep)
  -- x = native: always true via nativeLe.
  | native,    native    => isTrue (LessEq.refl _)
  | native,    cCompat   => isTrue (LessEq.nativeLe _)
  | native,    packed    => isTrue (LessEq.nativeLe _)
  | native,    bigEndian => isTrue (LessEq.nativeLe _)
  | native,    noSpec    => isTrue (LessEq.nativeLe _)
  -- y = noSpec (and x ≠ native handled above): always true via leNoSpec.
  | cCompat,   noSpec    => isTrue (LessEq.leNoSpec _)
  | packed,    noSpec    => isTrue (LessEq.leNoSpec _)
  | bigEndian, noSpec    => isTrue (LessEq.leNoSpec _)
  | noSpec,    noSpec    => isTrue (LessEq.refl _)
  -- Diagonal (x = y ≠ native, y ≠ noSpec): refl.
  | cCompat,   cCompat   => isTrue (LessEq.refl _)
  | packed,    packed    => isTrue (LessEq.refl _)
  | bigEndian, bigEndian => isTrue (LessEq.refl _)
  -- Off-diagonal, neither bottom nor top: false.
  | cCompat,   native    => isFalse (fun hContra => by cases hContra)
  | cCompat,   packed    => isFalse (fun hContra => by cases hContra)
  | cCompat,   bigEndian => isFalse (fun hContra => by cases hContra)
  | packed,    native    => isFalse (fun hContra => by cases hContra)
  | packed,    cCompat   => isFalse (fun hContra => by cases hContra)
  | packed,    bigEndian => isFalse (fun hContra => by cases hContra)
  | bigEndian, native    => isFalse (fun hContra => by cases hContra)
  | bigEndian, cCompat   => isFalse (fun hContra => by cases hContra)
  | bigEndian, packed    => isFalse (fun hContra => by cases hContra)
  | noSpec,    native    => isFalse (fun hContra => by cases hContra)
  | noSpec,    cCompat   => isFalse (fun hContra => by cases hContra)
  | noSpec,    packed    => isFalse (fun hContra => by cases hContra)
  | noSpec,    bigEndian => isFalse (fun hContra => by cases hContra)

/-! ### Commutativity and identity laws -/

theorem add_comm (leftRep rightRep : Representation) :
    add leftRep rightRep = add rightRep leftRep := by
  cases leftRep <;> cases rightRep <;> rfl

/-- Representation mul is commutative.  `mul := add` by definition,
    so this is a direct re-export of `add_comm`.  Used by the
    aggregate `Grade.mul_comm_of_same_provenance` (Q48/T7). -/
theorem mul_comm (leftRep rightRep : Representation) :
    mul leftRep rightRep = mul rightRep leftRep :=
  add_comm leftRep rightRep

theorem meet_comm (leftRep rightRep : Representation) :
    meet leftRep rightRep = meet rightRep leftRep := by
  cases leftRep <;> cases rightRep <;> rfl

theorem native_add (representation : Representation) : add native representation = some representation := by
  cases representation <;> rfl

theorem add_native (representation : Representation) : add representation native = some representation := by
  cases representation <;> rfl

theorem noSpec_add (representation : Representation) : add noSpec representation = some noSpec := by
  cases representation <;> rfl

theorem add_noSpec (representation : Representation) : add representation noSpec = some noSpec := by
  cases representation <;> rfl

theorem noSpec_meet (representation : Representation) : meet noSpec representation = some representation := by
  cases representation <;> rfl

theorem meet_noSpec (representation : Representation) : meet representation noSpec = some representation := by
  cases representation <;> rfl

theorem native_meet (representation : Representation) : meet native representation = some native := by
  cases representation <;> rfl

theorem meet_native (representation : Representation) : meet representation native = some native := by
  cases representation <;> rfl

/-- Idempotence — every element joins with itself to itself. -/
theorem add_idem (representation : Representation) : add representation representation = some representation := by
  cases representation <;> rfl

/-- Idempotence — every element meets with itself to itself. -/
theorem meet_idem (representation : Representation) : meet representation representation = some representation := by
  cases representation <;> rfl

/-- The validity predicate is symmetric (incompatibility is
    symmetric). -/
theorem valid_comm (leftRep rightRep : Representation) :
    isAddDefined leftRep rightRep ↔ isAddDefined rightRep leftRep := by
  unfold isAddDefined
  rw [add_comm]

theorem validMeet_comm (leftRep rightRep : Representation) :
    isMeetDefined leftRep rightRep ↔ isMeetDefined rightRep leftRep := by
  unfold isMeetDefined
  rw [meet_comm]

/--
The single invalid pair: `c` and `packed` cannot be jointly
satisfied.  This is error T047.
-/
theorem cCompat_packed_invalid : add cCompat packed = none := rfl

theorem packed_cCompat_invalid : add packed cCompat = none := rfl

theorem cCompat_packed_meet_invalid : meet cCompat packed = none := rfl

theorem packed_cCompat_meet_invalid : meet packed cCompat = none := rfl

end Representation

/-! ## TierL instance (T4)

Representation is the canonical Tier L dim: partial `joinOpt`
(`add`) and partial `meetOpt` (`meet`), with `none` on the
`c ⊔ packed` incompatibility.  Join commutes and is idempotent; meet
commutes.  Per §1.2 the carrier `default` is `native` (the
compiler-chooses bottom — most restrictive in that it imposes no
ABI commitment). -/
instance : TierL Representation where
  default        := Representation.native
  le             := Representation.LessEq
  le_refl        := Representation.LessEq.refl
  le_trans       := Representation.LessEq.trans
  joinOpt        := Representation.add
  meetOpt        := Representation.meet
  joinOpt_comm   := Representation.add_comm
  joinOpt_idem   := Representation.add_idem
  meetOpt_comm   := Representation.meet_comm

end FX.Kernel
