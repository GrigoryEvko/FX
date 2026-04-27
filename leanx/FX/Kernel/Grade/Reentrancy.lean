import FX.Kernel.Grade.Tier

/-!
# Reentrancy (dimension 19) — self-reference permission

Per `fx_design.md` §6.3 (dim 19).  Two-element chain
`nonReentrant ≤ reentrant`.

  * `nonReentrant` — default; compiler verifies no call path
                     from the function leads back to itself.
  * `reentrant`    — grant (`rec` or `with Reentrant`); self-
                     reference permitted, but a `decreases`
                     clause or `with Div` is mandatory (§5.2).

## Surface-syntax mapping

Per `fx_design.md` §6.3 dim 19 and §5.2:

  * (no annotation)    → `nonReentrant`  (default — deny self-ref)
  * `rec fn ...`       → `reentrant`     (grant; `decreases` or `with Div`)
  * `with Reentrant`   → `reentrant`     (alternative grant)

## Combining

Parallel/sequential combine is **join**: if any sub-expression
requires reentrancy, the enclosing expression is reentrant.

## Algebra

Same shape as `FpOrder` — 2-element idempotent commutative
monoid with `nonReentrant` as identity and `reentrant` as top.
-/

namespace FX.Kernel

inductive Reentrancy : Type where
  | nonReentrant : Reentrancy
  | reentrant    : Reentrancy
  deriving DecidableEq, Repr

namespace Reentrancy

def add : Reentrancy → Reentrancy → Reentrancy
  | nonReentrant,   rightReentrancy => rightReentrancy
  | leftReentrancy, nonReentrant    => leftReentrancy
  | reentrant,      reentrant       => reentrant

def mul : Reentrancy → Reentrancy → Reentrancy := add

inductive LessEq : Reentrancy → Reentrancy → Prop where
  | refl : ∀ reentrancy, LessEq reentrancy reentrancy
  | nrLe : LessEq nonReentrant reentrant

instance : LE Reentrancy := ⟨LessEq⟩

theorem LessEq.trans {leftReentrancy midReentrancy rightReentrancy : Reentrancy}
    (leftLeMid : leftReentrancy ≤ midReentrancy)
    (midLeRight : midReentrancy ≤ rightReentrancy) :
    leftReentrancy ≤ rightReentrancy := by
  cases leftLeMid with
  | refl => exact midLeRight
  | nrLe =>
    cases midLeRight with
    | refl => exact LessEq.nrLe

instance decLe : (leftReentrancy rightReentrancy : Reentrancy) →
    Decidable (LessEq leftReentrancy rightReentrancy)
  | nonReentrant, nonReentrant => isTrue (LessEq.refl _)
  | nonReentrant, reentrant    => isTrue LessEq.nrLe
  | reentrant,    nonReentrant => isFalse (fun contra => by cases contra)
  | reentrant,    reentrant    => isTrue (LessEq.refl _)

theorem add_comm (leftReentrancy rightReentrancy : Reentrancy) :
    add leftReentrancy rightReentrancy = add rightReentrancy leftReentrancy := by
  cases leftReentrancy <;> cases rightReentrancy <;> rfl

theorem add_assoc (leftReentrancy midReentrancy rightReentrancy : Reentrancy) :
    add (add leftReentrancy midReentrancy) rightReentrancy
      = add leftReentrancy (add midReentrancy rightReentrancy) := by
  cases leftReentrancy <;> cases midReentrancy <;> cases rightReentrancy <;> rfl

theorem add_idem (reentrancy : Reentrancy) : add reentrancy reentrancy = reentrancy := by
  cases reentrancy <;> rfl

theorem nonReentrant_add (reentrancy : Reentrancy) :
    add nonReentrant reentrancy = reentrancy := by
  cases reentrancy <;> rfl

theorem add_nonReentrant (reentrancy : Reentrancy) :
    add reentrancy nonReentrant = reentrancy := by
  cases reentrancy <;> rfl

theorem mul_assoc (leftReentrancy midReentrancy rightReentrancy : Reentrancy) :
    mul (mul leftReentrancy midReentrancy) rightReentrancy
      = mul leftReentrancy (mul midReentrancy rightReentrancy) :=
  add_assoc leftReentrancy midReentrancy rightReentrancy

theorem mul_idem (reentrancy : Reentrancy) : mul reentrancy reentrancy = reentrancy :=
  add_idem reentrancy

/-- Reentrancy mul is commutative — `mul := add := join` and
    `add_comm` is already proven.  Used by tier-generic theorems
    over `TierSComm` (T2/T7). -/
theorem mul_comm (leftReentrancy rightReentrancy : Reentrancy) :
    mul leftReentrancy rightReentrancy = mul rightReentrancy leftReentrancy :=
  add_comm leftReentrancy rightReentrancy

/-- Distributivity is degenerate under `add = mul = join`. -/
theorem left_distrib (leftReentrancy midReentrancy rightReentrancy : Reentrancy) :
    mul leftReentrancy (add midReentrancy rightReentrancy)
      = add (mul leftReentrancy midReentrancy) (mul leftReentrancy rightReentrancy) := by
  cases leftReentrancy <;> cases midReentrancy <;> cases rightReentrancy <;> rfl
theorem right_distrib (leftReentrancy midReentrancy rightReentrancy : Reentrancy) :
    mul (add leftReentrancy midReentrancy) rightReentrancy
      = add (mul leftReentrancy rightReentrancy) (mul midReentrancy rightReentrancy) := by
  cases leftReentrancy <;> cases midReentrancy <;> cases rightReentrancy <;> rfl

/-- Antisymmetry — `LessEq` is a genuine partial order. -/
theorem LessEq.antisymm {leftReentrancy rightReentrancy : Reentrancy}
    (leftLeRight : leftReentrancy ≤ rightReentrancy)
    (rightLeLeft : rightReentrancy ≤ leftReentrancy) :
    leftReentrancy = rightReentrancy := by
  cases leftLeRight with
  | refl => rfl
  | nrLe => cases rightLeLeft

/-- `reentrant` is the top: every grade subsumes into `reentrant`. -/
theorem le_reentrant (reentrancy : Reentrancy) : reentrancy ≤ reentrant := by
  cases reentrancy
  · exact LessEq.nrLe
  · exact LessEq.refl _

/-- `nonReentrant` is the bottom: it subsumes into every grade. -/
theorem nonReentrant_le (reentrancy : Reentrancy) : nonReentrant ≤ reentrancy := by
  cases reentrancy
  · exact LessEq.refl _
  · exact LessEq.nrLe

/-- `reentrant` absorbs into either side of `add`. -/
theorem add_reentrant_left  (reentrancy : Reentrancy) :
    add reentrant reentrancy = reentrant := by
  cases reentrancy <;> rfl
theorem add_reentrant_right (reentrancy : Reentrancy) :
    add reentrancy reentrant = reentrant := by
  cases reentrancy <;> rfl

/-- Monotonicity of `add`. -/
theorem add_mono_left {leftReentrancy leftReentrancyPrime : Reentrancy}
    (rightReentrancy : Reentrancy)
    (leftLePrime : leftReentrancy ≤ leftReentrancyPrime) :
    add leftReentrancy rightReentrancy ≤ add leftReentrancyPrime rightReentrancy := by
  cases leftReentrancy <;> cases leftReentrancyPrime <;> cases rightReentrancy <;>
    first
      | exact LessEq.refl _
      | exact LessEq.nrLe
      | (cases leftLePrime)

end Reentrancy

/-! ## TierSIdem instance (T2)

Reentrancy fits the idempotent join-lattice shape: `add = mul = join`
on `{nonReentrant < reentrant}`, `nonReentrant` is identity,
`reentrant` absorbs.  No strict annihilator. -/
instance : TierSIdem Reentrancy where
  default      := Reentrancy.nonReentrant
  le           := Reentrancy.LessEq
  le_refl      := Reentrancy.LessEq.refl
  le_trans     := Reentrancy.LessEq.trans
  add          := Reentrancy.add
  mul          := Reentrancy.mul
  zero         := Reentrancy.nonReentrant
  add_comm     := Reentrancy.add_comm
  add_assoc    := Reentrancy.add_assoc
  add_zero     := Reentrancy.add_nonReentrant
  zero_add     := Reentrancy.nonReentrant_add
  mul_assoc    := Reentrancy.mul_assoc
  mul_comm     := Reentrancy.mul_comm
  add_idem     := Reentrancy.add_idem
  mul_eq_add   := fun _ _ => rfl

end FX.Kernel
