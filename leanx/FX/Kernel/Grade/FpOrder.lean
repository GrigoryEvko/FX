import FX.Kernel.Grade.Tier

/-!
# FpOrder (dimension 17) — floating-point association freedom

Per `fx_design.md` §6.3 (dim 17).  Two-element chain
`strict ≤ reassociate`.

  * `strict`      — left-to-right evaluation, bit-identical
                    results across platforms.  Default.
  * `reassociate` — grant; compiler may reorder FP operations
                    for SIMD vectorization.

## Surface-syntax mapping

Per `fx_design.md` §3.11 and §6.3 dim 17, the source controls
map as follows:

  * (no annotation)       → `strict`       (default)
  * `with Reassociate`    → `reassociate`  (explicit grant to reorder)

Strict is the default because reassociation changes results
(e.g., `(a + b) + c ≠ a + (b + c)` under IEEE 754), so the grant
must be explicit.

## Combining

Parallel/sequential combine is **join** (max): if any part of
the expression is marked `reassociate`, the enclosing expression
may reorder.  `strict` is the unit (combining strict with
anything preserves the other side's annotation).

## Algebra

Idempotent commutative monoid for both `add` and `mul`, both
being `max`.  `strict` is the bottom (identity); `reassociate` is
the top.
-/

namespace FX.Kernel

inductive FpOrder : Type where
  | strict      : FpOrder
  | reassociate : FpOrder
  deriving DecidableEq, Repr

namespace FpOrder

/-- Join (max): grant propagates. -/
def add : FpOrder → FpOrder → FpOrder
  | strict,      rightFpOrder => rightFpOrder
  | leftFpOrder, strict       => leftFpOrder
  | reassociate, reassociate  => reassociate

def mul : FpOrder → FpOrder → FpOrder := add

inductive LessEq : FpOrder → FpOrder → Prop where
  | refl     : ∀ order, LessEq order order
  | strictLe : LessEq strict reassociate

instance : LE FpOrder := ⟨LessEq⟩

theorem LessEq.trans {leftFpOrder midFpOrder rightFpOrder : FpOrder}
    (leftLeMid : leftFpOrder ≤ midFpOrder) (midLeRight : midFpOrder ≤ rightFpOrder) :
    leftFpOrder ≤ rightFpOrder := by
  cases leftLeMid with
  | refl     => exact midLeRight
  | strictLe =>
    cases midLeRight with
    | refl => exact LessEq.strictLe

instance decLe : (leftFpOrder rightFpOrder : FpOrder) → Decidable (LessEq leftFpOrder rightFpOrder)
  | strict,      strict      => isTrue (LessEq.refl _)
  | strict,      reassociate => isTrue LessEq.strictLe
  | reassociate, strict      => isFalse (fun contra => by cases contra)
  | reassociate, reassociate => isTrue (LessEq.refl _)

theorem add_comm (leftFpOrder rightFpOrder : FpOrder) :
    add leftFpOrder rightFpOrder = add rightFpOrder leftFpOrder := by
  cases leftFpOrder <;> cases rightFpOrder <;> rfl

theorem add_assoc (leftFpOrder midFpOrder rightFpOrder : FpOrder) :
    add (add leftFpOrder midFpOrder) rightFpOrder
      = add leftFpOrder (add midFpOrder rightFpOrder) := by
  cases leftFpOrder <;> cases midFpOrder <;> cases rightFpOrder <;> rfl

theorem add_idem (order : FpOrder) : add order order = order := by cases order <;> rfl

theorem strict_add (order : FpOrder) : add strict order = order := by cases order <;> rfl

theorem add_strict (order : FpOrder) : add order strict = order := by cases order <;> rfl

theorem mul_assoc (leftFpOrder midFpOrder rightFpOrder : FpOrder) :
    mul (mul leftFpOrder midFpOrder) rightFpOrder
      = mul leftFpOrder (mul midFpOrder rightFpOrder) :=
  add_assoc leftFpOrder midFpOrder rightFpOrder

theorem mul_idem (order : FpOrder) : mul order order = order := add_idem order

/-- FpOrder mul is commutative.  Tier S idempotent semiring with
    `mul := add`, so this is a definitional re-export of
    `add_comm`.  Q48. -/
theorem mul_comm (leftFpOrder rightFpOrder : FpOrder) :
    mul leftFpOrder rightFpOrder = mul rightFpOrder leftFpOrder :=
  add_comm leftFpOrder rightFpOrder

/-- Distributivity is degenerate under `add = mul = join`. -/
theorem left_distrib (leftFpOrder midFpOrder rightFpOrder : FpOrder) :
    mul leftFpOrder (add midFpOrder rightFpOrder)
      = add (mul leftFpOrder midFpOrder) (mul leftFpOrder rightFpOrder) := by
  cases leftFpOrder <;> cases midFpOrder <;> cases rightFpOrder <;> rfl
theorem right_distrib (leftFpOrder midFpOrder rightFpOrder : FpOrder) :
    mul (add leftFpOrder midFpOrder) rightFpOrder
      = add (mul leftFpOrder rightFpOrder) (mul midFpOrder rightFpOrder) := by
  cases leftFpOrder <;> cases midFpOrder <;> cases rightFpOrder <;> rfl

/-- Antisymmetry — `LessEq` is a genuine partial order. -/
theorem LessEq.antisymm {leftFpOrder rightFpOrder : FpOrder}
    (leftLeRight : leftFpOrder ≤ rightFpOrder) (rightLeLeft : rightFpOrder ≤ leftFpOrder) :
    leftFpOrder = rightFpOrder := by
  cases leftLeRight with
  | refl     => rfl
  | strictLe => cases rightLeLeft

/-- `reassociate` is the top: every grade subsumes into `reassociate`. -/
theorem le_reassociate (order : FpOrder) : order ≤ reassociate := by
  cases order
  · exact LessEq.strictLe
  · exact LessEq.refl _

/-- `strict` is the bottom: `strict` subsumes into every grade. -/
theorem strict_le (order : FpOrder) : strict ≤ order := by
  cases order
  · exact LessEq.refl _
  · exact LessEq.strictLe

/-- `reassociate` absorbs into either side of `add`.  Grants
    propagate: once any subexpression permits reassociation, the
    whole expression does. -/
theorem add_reassociate_left  (order : FpOrder) :
    add reassociate order = reassociate := by
  cases order <;> rfl
theorem add_reassociate_right (order : FpOrder) :
    add order reassociate = reassociate := by
  cases order <;> rfl

/-- Monotonicity of `add`. -/
theorem add_mono_left {leftFpOrder leftFpOrderPrime : FpOrder} (rightFpOrder : FpOrder)
    (leftLePrime : leftFpOrder ≤ leftFpOrderPrime) :
    add leftFpOrder rightFpOrder ≤ add leftFpOrderPrime rightFpOrder := by
  cases leftFpOrder <;> cases leftFpOrderPrime <;> cases rightFpOrder <;>
    first
      | exact LessEq.refl _
      | exact LessEq.strictLe
      | (cases leftLePrime)

end FpOrder

/-! ## TierSIdem instance (T2)

FpOrder fits the idempotent join-lattice shape: `add = mul = max` on
`{strict < reassociate}`, `strict` is the bottom identity,
`reassociate` absorbs.  No strict annihilator. -/
instance : TierSIdem FpOrder where
  default      := FpOrder.strict
  le           := FpOrder.LessEq
  le_refl      := FpOrder.LessEq.refl
  le_trans     := FpOrder.LessEq.trans
  add          := FpOrder.add
  mul          := FpOrder.mul
  zero         := FpOrder.strict
  add_comm     := FpOrder.add_comm
  add_assoc    := FpOrder.add_assoc
  add_zero     := FpOrder.add_strict
  zero_add     := FpOrder.strict_add
  mul_assoc    := FpOrder.mul_assoc
  mul_comm     := FpOrder.mul_comm
  add_idem     := FpOrder.add_idem
  mul_eq_add   := fun _ _ => rfl

end FX.Kernel
