import FX.Kernel.Grade.Tier

/-!
# Complexity (dimension 13) — declared operation-count budget

Per `fx_design.md` §6.3 (dim 13).  Tracks the declared
asymptotic / concrete cost budget of an expression.  Naturals
with addition: `0` = free, `cost(f) + cost(g)` = combined.
The preorder is standard `≤` on `Nat`; a tighter bound is
usable where a looser one is expected (subsumption).

  * `0`    — free (unit element).  The default; an expression
             with no declared cost is assumed to have none.
  * `n`    — declared bound of `n` operations.  The compiler
             verifies every call path stays within the bound.

## Surface-syntax mapping

Per `fx_design.md` §6.3 dim 13 the grant is:

  * (no annotation)        → `0`      (free; default)
  * `cost N`               → `N`      (declared budget of N ops)
  * `unbounded`            → `omega`-like — currently encoded as
                              a special value not in this file's
                              carrier.  Phase 2.2 deliberately
                              leaves `unbounded` unrepresented
                              because the kernel's `Nat` is
                              total-bounded; `unbounded` lands
                              once the declared-budget-validator
                              ships in Stream E.

## Algebra

Both `add` and `mul` are natural-number addition — parallel
branches sum their worst-case costs, sequential composition
sums per §6.3.  `0` is the unit element for both.  Unlike
true semirings (e.g. Nat with `+`/`*`), here `*` is `+` because
cost composition is additive regardless of whether a call is
parallel or sequential — a cost-n function applied to a cost-m
argument costs n+m total in call-by-value.

  * add n m   = n + m
  * mul n m   = n + m   (sequential composition is additive)
  * n ≤ m iff Nat.le n m

Idempotence does NOT hold (`cost 2 + cost 2 = cost 4 ≠ cost 2`).
The dimension is a commutative monoid, not a lattice; the
order-theoretic subsumption still makes sense (tighter bound
stronger than looser).
-/

namespace FX.Kernel

/-- The complexity grade — a declared operation-count budget.
    `Nat` is the carrier; `0` is the unit element. -/
abbrev Complexity : Type := Nat

namespace Complexity

/-- Parallel combine — worst-case cost across branches sums. -/
def add (leftCost rightCost : Complexity) : Complexity := leftCost + rightCost

/-- Sequential combine — cost of `f(a)` is `cost(f) + cost(a)`
    in call-by-value.  Same as `add` per §6.3. -/
def mul (leftCost rightCost : Complexity) : Complexity := leftCost + rightCost

/-- Subsumption: a smaller budget can stand in where a larger
    one is expected.  `n ≤ m` iff `Nat.le n m`. -/
abbrev LessEq : Complexity → Complexity → Prop := Nat.le

instance : LE Complexity := inferInstance

-- `Nat` already provides `refl` and `trans` as `Nat.le_refl`
-- and `Nat.le_trans`; we re-export under the dimension-local
-- names the Grade aggregator uses.
theorem LessEq.refl (cost : Complexity) : cost ≤ cost := Nat.le_refl cost

theorem LessEq.trans {lowerCost middleCost upperCost : Complexity}
    (lowerLeMiddle : lowerCost ≤ middleCost)
    (middleLeUpper : middleCost ≤ upperCost) :
    lowerCost ≤ upperCost :=
  Nat.le_trans lowerLeMiddle middleLeUpper

/-! ## Laws -/

theorem add_comm (leftCost rightCost : Complexity) :
    add leftCost rightCost = add rightCost leftCost :=
  Nat.add_comm _ _

theorem add_assoc (leftCost middleCost rightCost : Complexity) :
    add (add leftCost middleCost) rightCost
      = add leftCost (add middleCost rightCost) :=
  Nat.add_assoc _ _ _

theorem zero_add (cost : Complexity) : add 0 cost = cost := Nat.zero_add _

theorem add_zero (cost : Complexity) : add cost 0 = cost := Nat.add_zero _

theorem mul_assoc (leftCost middleCost rightCost : Complexity) :
    mul (mul leftCost middleCost) rightCost
      = mul leftCost (mul middleCost rightCost) :=
  add_assoc _ _ _

/-- Complexity mul is commutative.  `mul := add := Nat.(+)`, so
    this is a definitional re-export of `Nat.add_comm`.  Named here
    so the aggregate `Grade.mul_comm_of_same_provenance` (T7/T9)
    references it uniformly alongside the other dims' `mul_comm`s
    rather than inlining `Nat.add_comm` at the call site. -/
theorem mul_comm (leftCost rightCost : Complexity) :
    mul leftCost rightCost = mul rightCost leftCost :=
  Nat.add_comm _ _

/-- Monotonicity of `add` — larger inputs produce larger sums. -/
theorem add_mono_left {leftCost leftCostPrime : Complexity} (rightCost : Complexity)
    (leftLePrime : leftCost ≤ leftCostPrime) :
    add leftCost rightCost ≤ add leftCostPrime rightCost :=
  Nat.add_le_add_right leftLePrime _

theorem add_mono_right {rightCost rightCostPrime : Complexity} (leftCost : Complexity)
    (rightLePrime : rightCost ≤ rightCostPrime) :
    add leftCost rightCost ≤ add leftCost rightCostPrime :=
  Nat.add_le_add_left rightLePrime _

end Complexity

/-! ## TierSComm instance (T2)

Complexity fits the Nat-additive-monoid shape: `add = mul = Nat.(+)`,
`0` is the additive identity and also the degenerate mul-identity
(`0 + x = x`, which is also `mul 0 x = x` since `mul := add`).  The
strict semiring law `zero_mul : mul 0 x = 0` does NOT hold — `mul 0
x = x`, not `0` — so Complexity is NOT a `TierSRing`.  It instances
`TierSComm` but not `TierSIdem` (no idempotence: `n + n = 2n ≠ n`).

Per §1.2 the carrier `default` is `0` (no declared cost budget =
most restrictive). -/
instance : TierSComm Complexity where
  default      := 0
  le           := Complexity.LessEq
  le_refl      := Complexity.LessEq.refl
  le_trans     := Complexity.LessEq.trans
  add          := Complexity.add
  mul          := Complexity.mul
  zero         := 0
  add_comm     := Complexity.add_comm
  add_assoc    := Complexity.add_assoc
  add_zero     := Complexity.add_zero
  zero_add     := Complexity.zero_add
  mul_assoc    := Complexity.mul_assoc
  mul_comm     := Complexity.mul_comm

end FX.Kernel
