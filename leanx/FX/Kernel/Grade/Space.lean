import FX.Kernel.Grade.Tier

/-!
# Space (dimension 15) — declared allocation budget

Per `fx_design.md` §6.3 (dim 15) and §8.2 (allocation
strategies).  Tracks the declared bound on heap / region /
stack allocation of an expression.  Naturals with addition:
`0` = no allocation (stack-only code), `n` = at most `n` bytes
(or slots) allocated.

  * `0`    — no allocation.  Default for expressions with no
             `with Alloc(...)` grant.  Compile-time guaranteed
             heap-free path.
  * `n`    — at most `n` bytes (or slots) allocated along any
             path.  Composed additively through `+`.

## Surface-syntax mapping

Per `fx_design.md` §6.3 dim 15 + §8.2:

  * (no annotation)                → `0`   (stack-only default)
  * `with Alloc(Stack, bound: N)`  → `N`   (stack-allocated N bytes)
  * `with Alloc(Region(r))`         → `n`   (region-bounded; bound
                                              inferred from region
                                              size once A8 region
                                              tracking integrates)
  * `with Alloc(Slab)`              → `n`   (per-type slab size
                                              known at comptime)

The default is `0` because the design doc's principle (§1.2
"deny by default, grant by permission") says an unannotated fn
must not allocate; the explicit `Alloc` grants name the strategy
and bound.

## Algebra

Identical shape to Complexity (dim 13): naturals with addition,
`0` as unit, subsumption by `Nat.le`.  Both `add` (parallel)
and `mul` (sequential) sum — memory consumed is additive
regardless of whether branches run in parallel or in sequence.

  * add n m   = n + m
  * mul n m   = n + m
  * n ≤ m iff Nat.le n m

Idempotence does NOT hold (allocating n bytes twice costs 2n,
not n).  This is a commutative monoid, not a lattice.
-/

namespace FX.Kernel

/-- The space grade — a declared allocation budget.  `Nat` is
    the carrier; `0` means no allocation, the default. -/
abbrev Space : Type := Nat

namespace Space

/-- Parallel combine — worst-case allocation sums across
    branches.  Matches Complexity's treatment. -/
def add (leftSpace rightSpace : Space) : Space := leftSpace + rightSpace

/-- Sequential combine — same as `add`; allocation is additive
    through composition regardless of branch vs sequence. -/
def mul (leftSpace rightSpace : Space) : Space := leftSpace + rightSpace

/-- Subsumption: a smaller allocation budget can stand in where
    a larger one is expected. -/
abbrev LessEq : Space → Space → Prop := Nat.le

instance : LE Space := inferInstance

theorem LessEq.refl (space : Space) : space ≤ space := Nat.le_refl space

theorem LessEq.trans {lowerSpace middleSpace upperSpace : Space}
    (lowerLeMiddle : lowerSpace ≤ middleSpace)
    (middleLeUpper : middleSpace ≤ upperSpace) :
    lowerSpace ≤ upperSpace :=
  Nat.le_trans lowerLeMiddle middleLeUpper

/-! ## Laws -/

theorem add_comm (leftSpace rightSpace : Space) :
    add leftSpace rightSpace = add rightSpace leftSpace :=
  Nat.add_comm _ _

theorem add_assoc (leftSpace middleSpace rightSpace : Space) :
    add (add leftSpace middleSpace) rightSpace
      = add leftSpace (add middleSpace rightSpace) :=
  Nat.add_assoc _ _ _

theorem zero_add (space : Space) : add 0 space = space := Nat.zero_add _

theorem add_zero (space : Space) : add space 0 = space := Nat.add_zero _

theorem mul_assoc (leftSpace middleSpace rightSpace : Space) :
    mul (mul leftSpace middleSpace) rightSpace
      = mul leftSpace (mul middleSpace rightSpace) :=
  add_assoc _ _ _

/-- Space mul is commutative.  `mul := add := Nat.(+)`; named
    for uniform reference in the aggregate proof (T7/T9). -/
theorem mul_comm (leftSpace rightSpace : Space) :
    mul leftSpace rightSpace = mul rightSpace leftSpace :=
  Nat.add_comm _ _

/-- Monotonicity — stacking more into either operand raises
    the sum. -/
theorem add_mono_left {leftSpace leftSpacePrime : Space} (rightSpace : Space)
    (leftLePrime : leftSpace ≤ leftSpacePrime) :
    add leftSpace rightSpace ≤ add leftSpacePrime rightSpace :=
  Nat.add_le_add_right leftLePrime _

theorem add_mono_right {rightSpace rightSpacePrime : Space} (leftSpace : Space)
    (rightLePrime : rightSpace ≤ rightSpacePrime) :
    add leftSpace rightSpace ≤ add leftSpace rightSpacePrime :=
  Nat.add_le_add_left rightLePrime _

end Space

/-! ## TierSComm instance (T2)

Space has the same Nat-additive-monoid shape as Complexity/Precision:
`add = mul = Nat.(+)`, no zero-mul annihilator, no idempotence.
Instances `TierSComm` only. -/
instance : TierSComm Space where
  default      := 0
  le           := Space.LessEq
  le_refl      := Space.LessEq.refl
  le_trans     := Space.LessEq.trans
  add          := Space.add
  mul          := Space.mul
  zero         := 0
  add_comm     := Space.add_comm
  add_assoc    := Space.add_assoc
  add_zero     := Space.add_zero
  zero_add     := Space.zero_add
  mul_assoc    := Space.mul_assoc
  mul_comm     := Space.mul_comm

end FX.Kernel
