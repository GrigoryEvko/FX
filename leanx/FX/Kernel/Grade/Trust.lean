import FX.Kernel.Grade.Tier

/-!
# Trust (dimension 9) — call-graph verification level

Per `fx_design.md` §6.3 (dim 9).  Tier S in the design doc; the
structure is actually an **idempotent commutative semiring with
`min` as both + and *** — the unusual case where the operation is
genuinely a lattice meet and both monoid laws are satisfied by
the total chain with `Verified` as the top and `External` as the
bottom.

## The chain

Ordered top-down (most-trusted first):

    Verified  >  Tested  >  Sorry  >  Assumed  >  External

  * `verified` — full machine proof of all specifications.
  * `tested`   — property-tested but not proved.
  * `sorry`    — contains `sorry` placeholder (dev builds only).
  * `assumed`  — postulated via `axiom` (mathematical assumption).
  * `external` — FFI / IO / deserialization boundary; trust unknown.

## Surface-syntax mapping

Per `fx_design.md` §6.3 dim 9 and §10.6:

  * (verified body, no `sorry`/`axiom`) → `verified`
  * `@[tested]` / property-test coverage → `tested`
  * `sorry` in body                     → `sorryT`
  * `axiom` declaration                 → `assumed`
  * `extern "C"` / deserializer output  → `external`

## Algebra

Combining trust levels follows the **weakest-link** rule:
calling a function with trust `T'` from a function with trust `T`
gives the caller trust `min(T, T')`.  This is the meet in the
lattice where `Verified` is top.

  * `add = min` (parallel: take weakest)
  * `mul = min` (sequential: take weakest)
  * `0 = Verified` (additive identity *and* top; note that this
    differs from other dimensions where 0 is bottom)
  * `1 = Verified` (multiplicative identity)

Under `min`:
  * `0 + x = min(Verified, x) = x` ✓
  * `0 * x = min(Verified, x) = x` — **not** an annihilator.
  * `1 * x = min(Verified, x) = x` ✓

So Trust is an **idempotent commutative monoid** for both ops
but not a semiring with a zero annihilator.  The release-build
policy (§10.6: `fxc --release` requires `trust ≥ Verified`) is
enforced by `LessEq` below, not by the monoid structure.

## Axioms realized

Grade-subsumption via `LessEq`; Grade-semiring-laws in the weakened
(idempotent comm monoid) sense.
-/

namespace FX.Kernel

/--
Trust levels, listed bottom-to-top so Lean's auto-derived
`DecidableEq` is straightforward.  For the lattice order use
`LessEq` below — the declaration order of constructors is *not* the
mathematical order.
-/
inductive Trust : Type where
  | external : Trust   -- bottom
  | assumed  : Trust
  | sorryT   : Trust   -- `sorry` is a Lean keyword, so renamed
  | tested   : Trust
  | verified : Trust   -- top
  deriving DecidableEq, Repr

/-- `Inhabited` via `tested` — the default for freshly-elaborated
    decls in `GlobalEntry` (strong enough to be believed after
    type-checking but weak enough to require explicit upgrade to
    `verified` for release builds). -/
instance : Inhabited Trust := ⟨Trust.tested⟩

namespace Trust

/--
Map each level to its rank in the chain (0 = bottom, 4 = top).
This is the canonical embedding into `Nat` that makes the
lattice operations computable.
-/
def rank : Trust → Nat
  | external => 0
  | assumed  => 1
  | sorryT   => 2
  | tested   => 3
  | verified => 4

/-- Recover the `Trust` constructor from a rank.  Defined for all
    `Nat` to keep it total; out-of-range maps to `verified`
    (the top of the chain). -/
def ofRank : Nat → Trust
  | 0 => external
  | 1 => assumed
  | 2 => sorryT
  | 3 => tested
  | _ => verified

theorem ofRank_rank (trust : Trust) : ofRank (rank trust) = trust := by
  cases trust <;> rfl

/-- `rank` is injective on `Trust` — the five constructors map
    to five distinct naturals.  Corollary of `ofRank_rank`. -/
theorem rank_injective {leftTrust rightTrust : Trust}
    (ranksEq : rank leftTrust = rank rightTrust) : leftTrust = rightTrust := by
  have roundTrip : ofRank (rank leftTrust) = ofRank (rank rightTrust) := by
    rw [ranksEq]
  rw [ofRank_rank, ofRank_rank] at roundTrip
  exact roundTrip

/-- Meet: weakest link.  Since `rank` is injective on the chain,
    `min` on ranks transports the operation. -/
def min : Trust → Trust → Trust
  | external, _ => external
  | _, external => external
  | assumed,  _ => assumed
  | _, assumed  => assumed
  | sorryT,   _ => sorryT
  | _, sorryT   => sorryT
  | tested,   _ => tested
  | _, tested   => tested
  | verified, verified => verified

/-- Parallel combine — meet (weakest link). -/
def add : Trust → Trust → Trust := min

/-- Sequential combine — also meet (caller's trust through a
    low-trust callee is the callee's trust). -/
def mul : Trust → Trust → Trust := min

/--
Subsumption: `x ≤ y` iff `x` is at *most* as strong as `y`.

If a function declares itself `verified`, it may be called from
any context (subsumption up to `verified` is always safe).  If a
function is `external`, it cannot be called from a context that
requires `verified`.  Direction: weaker ≤ stronger.
-/
def LessEq (leftTrust rightTrust : Trust) : Prop :=
  rank leftTrust ≤ rank rightTrust

instance : LE Trust := ⟨LessEq⟩

theorem LessEq.refl (trust : Trust) : trust ≤ trust := Nat.le_refl _

theorem LessEq.trans {lowerTrust middleTrust upperTrust : Trust}
    (lowerLeMiddle : lowerTrust ≤ middleTrust)
    (middleLeUpper : middleTrust ≤ upperTrust) : lowerTrust ≤ upperTrust :=
  Nat.le_trans lowerLeMiddle middleLeUpper

/-- Antisymmetry — `LessEq` is a genuine partial order. -/
theorem LessEq.antisymm {leftTrust rightTrust : Trust}
    (leftLeRight : leftTrust ≤ rightTrust)
    (rightLeLeft : rightTrust ≤ leftTrust) : leftTrust = rightTrust :=
  rank_injective (Nat.le_antisymm leftLeRight rightLeLeft)

instance decLe (leftTrust rightTrust : Trust) : Decidable (LessEq leftTrust rightTrust) :=
  inferInstanceAs (Decidable (rank leftTrust ≤ rank rightTrust))

/-! ### Idempotent commutative monoid laws -/

theorem add_comm (leftTrust rightTrust : Trust) :
    add leftTrust rightTrust = add rightTrust leftTrust := by
  cases leftTrust <;> cases rightTrust <;> rfl

theorem add_assoc (leftTrust middleTrust rightTrust : Trust) :
    add (add leftTrust middleTrust) rightTrust
      = add leftTrust (add middleTrust rightTrust) := by
  cases leftTrust <;> cases middleTrust <;> cases rightTrust <;> rfl

theorem add_idem (trust : Trust) : add trust trust = trust := by
  cases trust <;> rfl

/-- `verified` is the identity for `min` (top of the chain). -/
theorem verified_add (trust : Trust) : add verified trust = trust := by
  cases trust <;> rfl

theorem add_verified (trust : Trust) : add trust verified = trust := by
  cases trust <;> rfl

/-- `external` absorbs under `min` (bottom of the chain). -/
theorem external_add (trust : Trust) : add external trust = external := by
  cases trust <;> rfl

theorem add_external (trust : Trust) : add trust external = external := by
  cases trust <;> rfl

theorem mul_assoc (leftTrust middleTrust rightTrust : Trust) :
    mul (mul leftTrust middleTrust) rightTrust
      = mul leftTrust (mul middleTrust rightTrust) :=
  add_assoc leftTrust middleTrust rightTrust

/-- Trust mul is commutative.  `mul := min := add` and `add`
    is already proven commutative, so this is a definitional
    re-export.  Used by the aggregate
    `Grade.mul_comm_of_same_provenance` (Q48). -/
theorem mul_comm (leftTrust rightTrust : Trust) :
    mul leftTrust rightTrust = mul rightTrust leftTrust :=
  add_comm leftTrust rightTrust

theorem mul_idem (trust : Trust) : mul trust trust = trust := add_idem trust

theorem verified_mul (trust : Trust) : mul verified trust = trust :=
  verified_add trust

theorem mul_verified (trust : Trust) : mul trust verified = trust :=
  add_verified trust

/-- Idempotent distributivity collapses. -/
theorem left_distrib (leftTrust middleTrust rightTrust : Trust) :
    mul leftTrust (add middleTrust rightTrust)
      = add (mul leftTrust middleTrust) (mul leftTrust rightTrust) := by
  cases leftTrust <;> cases middleTrust <;> cases rightTrust <;> rfl

theorem right_distrib (leftTrust middleTrust rightTrust : Trust) :
    mul (add leftTrust middleTrust) rightTrust
      = add (mul leftTrust rightTrust) (mul middleTrust rightTrust) := by
  cases leftTrust <;> cases middleTrust <;> cases rightTrust <;> rfl

/-! ### Top / bottom universals -/

/-- `verified` is the top: every trust grade is ≤ `verified`.
    This is the positive form of §10.6 — release builds that
    require `verified` cannot be called from non-`verified`
    context, captured negatively by `¬ LessEq verified x` whenever
    `x ≠ verified`. -/
theorem le_verified (trust : Trust) : LessEq trust verified := by
  cases trust <;> decide

/-- `external` is the bottom: it subsumes into every grade. -/
theorem external_le (trust : Trust) : LessEq external trust := by
  cases trust <;> decide

/-! ### Monotonicity of `add` -/

theorem add_mono_left {smallerLeft largerLeft : Trust} (rightTrust : Trust)
    (leftLe : LessEq smallerLeft largerLeft) :
    LessEq (add smallerLeft rightTrust) (add largerLeft rightTrust) := by
  have rankLeftLe : rank smallerLeft ≤ rank largerLeft := leftLe
  cases smallerLeft <;> cases largerLeft <;> cases rightTrust <;>
    first
      | (exact LessEq.refl _)
      | (show LessEq _ _; decide)
      | (exfalso; simp [rank] at rankLeftLe)

theorem add_mono_right {smallerRight largerRight : Trust} (leftTrust : Trust)
    (rightLe : LessEq smallerRight largerRight) :
    LessEq (add leftTrust smallerRight) (add leftTrust largerRight) := by
  rw [add_comm leftTrust smallerRight, add_comm leftTrust largerRight]
  exact add_mono_left leftTrust rightLe

/-- Monotonicity of `mul` — inherited from `add` since `mul = add`. -/
theorem mul_mono_left {smallerLeft largerLeft : Trust} (rightTrust : Trust)
    (leftLe : LessEq smallerLeft largerLeft) :
    LessEq (mul smallerLeft rightTrust) (mul largerLeft rightTrust) :=
  add_mono_left rightTrust leftLe

theorem mul_mono_right {smallerRight largerRight : Trust} (leftTrust : Trust)
    (rightLe : LessEq smallerRight largerRight) :
    LessEq (mul leftTrust smallerRight) (mul leftTrust largerRight) :=
  add_mono_right leftTrust rightLe

end Trust

/-! ## TierSIdem instance (T2)

Trust fits the idempotent-with-meet shape: `add = mul = min` over the
5-element chain, `verified` is the meet-identity (`min verified x =
x`), `external` is the bottom absorber.  Strict annihilation fails
(`min verified x = x`, not `verified`).

Per §10.6 release builds gate on trust level; the carrier `default`
for a fresh binding is `verified` (the algebraic identity), so that
adding a new decl to the grade vector leaves existing trust
unchanged.  Note: this differs from `Inhabited Trust = tested`,
which represents the "post-typecheck, pre-proof" state a freshly-
elaborated decl starts at.  The two are distinct: `GradeCarrier
.default` is the algebraic identity; `Inhabited` is the post-elab
starting value. -/
instance : TierSIdem Trust where
  default      := Trust.verified
  le           := Trust.LessEq
  le_refl      := Trust.LessEq.refl
  le_trans     := Trust.LessEq.trans
  add          := Trust.add
  mul          := Trust.mul
  zero         := Trust.verified
  add_comm     := Trust.add_comm
  add_assoc    := Trust.add_assoc
  add_zero     := Trust.add_verified
  zero_add     := Trust.verified_add
  mul_assoc    := Trust.mul_assoc
  mul_comm     := Trust.mul_comm
  add_idem     := Trust.add_idem
  mul_eq_add   := fun _ _ => rfl

end FX.Kernel
