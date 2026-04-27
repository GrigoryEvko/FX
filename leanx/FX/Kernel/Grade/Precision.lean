import FX.Kernel.Grade.Tier

/-!
# Precision (dimension 14) — floating-point error bound

Per `fx_design.md` §6.3 (dim 14).  Tracks the declared
worst-case numerical error of an expression, measured in
units-in-the-last-place (ULPs).  Zero means "exact" — no
rounding error is permitted; larger values bound the
accumulated error.

  * `0`    — exact.  The default; an expression with no
             declared precision is exact (no float-flavoured
             rounding allowed).  Matches the surface `exact`
             annotation.
  * `n`    — declared upper bound of `n` ULPs of accumulated
             error.  The compiler verifies every composition
             path stays within the bound.

## Surface-syntax mapping

Per `fx_design.md` §3.11 (FP control) and §6.3 dim 14 the grant is:

  * (no annotation)                → `0`    (exact; default)
  * declared FP op yielding 1 ULP  → `1`    (single-op bound)
  * `with Precision(bound: N)`     → `N`    (carrier-level
                                             declared bound)

## Algebra

Phase-2 uses naive ULP accumulation: both `add` (parallel
branches — worst case across branches) and `mul` (sequential
composition — errors accumulate through a chain) are natural-
number addition.  Zero is the unit element for both operations.

  * add n m = n + m
  * mul n m = n + m   (sequential composition accumulates)
  * n ≤ m iff Nat.le n m

The spec (§6.3 dim 14) references condition-number-aware
accumulation (Higham §3.3) as the "right" composition rule —
properly handling catastrophic cancellation.  That's runtime-
value-dependent and not decidable at compile time; a static
grade needs a value-independent upper bound, and naive ULP
addition is the conservative choice.  A future revision may
track condition numbers alongside the ULP bound to tighten
the estimate when proofs of input ranges are available; until
then the present implementation matches the Tier-S pattern
used for Complexity and Space.

Idempotence does NOT hold (`1 + 1 = 2 ≠ 1`).  The dimension is
a commutative monoid, not a lattice; order-theoretic subsumption
still makes sense (tighter bound stronger than looser).
-/

namespace FX.Kernel

/-- The precision grade — a declared ULP error bound.  `Nat` is
    the carrier; `0` is the unit element (exact, no error). -/
abbrev Precision : Type := Nat

namespace Precision

/-- Parallel combine — worst-case error across branches sums. -/
def add (leftBound rightBound : Precision) : Precision :=
  leftBound + rightBound

/-- Sequential combine — composition of FP ops accumulates
    error additively in the naive-ULP model. -/
def mul (leftBound rightBound : Precision) : Precision :=
  leftBound + rightBound

/-- Subsumption: a tighter error bound can stand in where a
    looser one is expected.  `n ≤ m` iff `Nat.le n m`. -/
abbrev LessEq : Precision → Precision → Prop := Nat.le

instance : LE Precision := inferInstance

-- `Nat` already provides `refl` and `trans` as `Nat.le_refl`
-- and `Nat.le_trans`; we re-export under the dimension-local
-- names the Grade aggregator uses.
theorem LessEq.refl (bound : Precision) : bound ≤ bound := Nat.le_refl bound

theorem LessEq.trans {lowerBound middleBound upperBound : Precision}
    (lowerLeMiddle : lowerBound ≤ middleBound)
    (middleLeUpper : middleBound ≤ upperBound) :
    lowerBound ≤ upperBound :=
  Nat.le_trans lowerLeMiddle middleLeUpper

/-! ## Laws -/

theorem add_comm (leftBound rightBound : Precision) :
    add leftBound rightBound = add rightBound leftBound :=
  Nat.add_comm _ _

theorem add_assoc (leftBound middleBound rightBound : Precision) :
    add (add leftBound middleBound) rightBound
      = add leftBound (add middleBound rightBound) :=
  Nat.add_assoc _ _ _

theorem zero_add (bound : Precision) : add 0 bound = bound := Nat.zero_add _

theorem add_zero (bound : Precision) : add bound 0 = bound := Nat.add_zero _

theorem mul_assoc (leftBound middleBound rightBound : Precision) :
    mul (mul leftBound middleBound) rightBound
      = mul leftBound (mul middleBound rightBound) :=
  add_assoc _ _ _

/-- Precision mul is commutative.  `mul := add := Nat.(+)`; named
    for uniform reference in the aggregate proof (T7/T9). -/
theorem mul_comm (leftBound rightBound : Precision) :
    mul leftBound rightBound = mul rightBound leftBound :=
  Nat.add_comm _ _

/-- Monotonicity of `add` — larger inputs produce larger sums. -/
theorem add_mono_left {leftBound leftBoundPrime : Precision}
    (rightBound : Precision)
    (leftLePrime : leftBound ≤ leftBoundPrime) :
    add leftBound rightBound ≤ add leftBoundPrime rightBound :=
  Nat.add_le_add_right leftLePrime _

theorem add_mono_right {rightBound rightBoundPrime : Precision}
    (leftBound : Precision)
    (rightLePrime : rightBound ≤ rightBoundPrime) :
    add leftBound rightBound ≤ add leftBound rightBoundPrime :=
  Nat.add_le_add_left rightLePrime _

end Precision

/-! ## TierSComm instance (T2)

Precision has the same Nat-additive-monoid shape as Complexity:
`add = mul = Nat.(+)`, no zero-mul annihilator, no idempotence.
Instances `TierSComm` only. -/
instance : TierSComm Precision where
  default      := 0
  le           := Precision.LessEq
  le_refl      := Precision.LessEq.refl
  le_trans     := Precision.LessEq.trans
  add          := Precision.add
  mul          := Precision.mul
  zero         := 0
  add_comm     := Precision.add_comm
  add_assoc    := Precision.add_assoc
  add_zero     := Precision.add_zero
  zero_add     := Precision.zero_add
  mul_assoc    := Precision.mul_assoc
  mul_comm     := Precision.mul_comm

end FX.Kernel
