import LeanFX2.Graded.Instances.Complexity

/-! # Graded/Instances/Space — allocation-strategy space semiring

`SpaceGrade` tracks the erased allocation-space dimension as a product:

* allocation strategy: stack < region < slab < pool < refcounted < heap
* byte bound: finite natural bound or `unbounded`

The old Nat wrapper was only a byte counter.  This carrier is faithful to
the FX requirement that space grades include both allocation strategy and
bounded-or-unbounded size information.

Operations:

* `0` = no allocation: stack strategy, zero bytes
* `1` = heap identity strategy, one byte unit for scaling
* `+` = worse allocation strategy plus byte-bound addition
* `*` = better allocation strategy plus byte-bound multiplication
* `≤` = product preorder

Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-! ## Allocation strategy chain -/

/-- Allocation strategy ordered from most restrictive to most general. -/
inductive AllocStrategy : Type
  /-- Stack allocation: bottom, no heap capability. -/
  | stack
  /-- Region allocation. -/
  | region
  /-- Slab allocation. -/
  | slab
  /-- Pool allocation. -/
  | pool
  /-- Reference-counted allocation. -/
  | refcounted
  /-- General heap allocation: top, multiplicative identity. -/
  | heap
  deriving DecidableEq, Repr

namespace AllocStrategy

/-- Combining allocation permissions keeps the more general strategy. -/
def add : AllocStrategy → AllocStrategy → AllocStrategy
  | .stack, rightStrategy => rightStrategy
  | .region, .stack => .region
  | .region, .region => .region
  | .region, .slab => .slab
  | .region, .pool => .pool
  | .region, .refcounted => .refcounted
  | .region, .heap => .heap
  | .slab, .stack => .slab
  | .slab, .region => .slab
  | .slab, .slab => .slab
  | .slab, .pool => .pool
  | .slab, .refcounted => .refcounted
  | .slab, .heap => .heap
  | .pool, .stack => .pool
  | .pool, .region => .pool
  | .pool, .slab => .pool
  | .pool, .pool => .pool
  | .pool, .refcounted => .refcounted
  | .pool, .heap => .heap
  | .refcounted, .stack => .refcounted
  | .refcounted, .region => .refcounted
  | .refcounted, .slab => .refcounted
  | .refcounted, .pool => .refcounted
  | .refcounted, .refcounted => .refcounted
  | .refcounted, .heap => .heap
  | .heap, .stack => .heap
  | .heap, .region => .heap
  | .heap, .slab => .heap
  | .heap, .pool => .heap
  | .heap, .refcounted => .heap
  | .heap, .heap => .heap

/-- Sequential allocation scaling keeps the more restrictive strategy;
stack annihilates and heap is identity. -/
def mul : AllocStrategy → AllocStrategy → AllocStrategy
  | .stack, .stack => .stack
  | .stack, .region => .stack
  | .stack, .slab => .stack
  | .stack, .pool => .stack
  | .stack, .refcounted => .stack
  | .stack, .heap => .stack
  | .region, .stack => .stack
  | .region, .region => .region
  | .region, .slab => .region
  | .region, .pool => .region
  | .region, .refcounted => .region
  | .region, .heap => .region
  | .slab, .stack => .stack
  | .slab, .region => .region
  | .slab, .slab => .slab
  | .slab, .pool => .slab
  | .slab, .refcounted => .slab
  | .slab, .heap => .slab
  | .pool, .stack => .stack
  | .pool, .region => .region
  | .pool, .slab => .slab
  | .pool, .pool => .pool
  | .pool, .refcounted => .pool
  | .pool, .heap => .pool
  | .refcounted, .stack => .stack
  | .refcounted, .region => .region
  | .refcounted, .slab => .slab
  | .refcounted, .pool => .pool
  | .refcounted, .refcounted => .refcounted
  | .refcounted, .heap => .refcounted
  | .heap, .stack => .stack
  | .heap, .region => .region
  | .heap, .slab => .slab
  | .heap, .pool => .pool
  | .heap, .refcounted => .refcounted
  | .heap, .heap => .heap

/-- Allocation-strategy subsumption. -/
def le : AllocStrategy → AllocStrategy → Prop
  | .stack, .stack => True
  | .stack, .region => True
  | .stack, .slab => True
  | .stack, .pool => True
  | .stack, .refcounted => True
  | .stack, .heap => True
  | .region, .stack => False
  | .region, .region => True
  | .region, .slab => True
  | .region, .pool => True
  | .region, .refcounted => True
  | .region, .heap => True
  | .slab, .stack => False
  | .slab, .region => False
  | .slab, .slab => True
  | .slab, .pool => True
  | .slab, .refcounted => True
  | .slab, .heap => True
  | .pool, .stack => False
  | .pool, .region => False
  | .pool, .slab => False
  | .pool, .pool => True
  | .pool, .refcounted => True
  | .pool, .heap => True
  | .refcounted, .stack => False
  | .refcounted, .region => False
  | .refcounted, .slab => False
  | .refcounted, .pool => False
  | .refcounted, .refcounted => True
  | .refcounted, .heap => True
  | .heap, .stack => False
  | .heap, .region => False
  | .heap, .slab => False
  | .heap, .pool => False
  | .heap, .refcounted => False
  | .heap, .heap => True

/-- Addition is associative on allocation strategies. -/
theorem add_assoc : ∀ first second third,
    add (add first second) third = add first (add second third) := by
  intro first second third
  cases first <;> cases second <;> cases third <;> rfl

/-- Addition is commutative on allocation strategies. -/
theorem add_comm : ∀ first second, add first second = add second first := by
  intro first second
  cases first <;> cases second <;> rfl

/-- Stack is the left additive identity. -/
theorem add_zero_left : ∀ value, add .stack value = value := by
  intro value
  cases value <;> rfl

/-- Stack is the right additive identity. -/
theorem add_zero_right : ∀ value, add value .stack = value := by
  intro value
  cases value <;> rfl

/-- Multiplication is associative on allocation strategies. -/
theorem mul_assoc : ∀ first second third,
    mul (mul first second) third = mul first (mul second third) := by
  intro first second third
  cases first <;> cases second <;> cases third <;> rfl

/-- Heap is the left multiplicative identity. -/
theorem mul_one_left : ∀ value, mul .heap value = value := by
  intro value
  cases value <;> rfl

/-- Heap is the right multiplicative identity. -/
theorem mul_one_right : ∀ value, mul value .heap = value := by
  intro value
  cases value <;> rfl

/-- Left distributivity of strategy meet over join. -/
theorem mul_distrib_left : ∀ scalar leftAddend rightAddend,
    mul scalar (add leftAddend rightAddend) =
      add (mul scalar leftAddend) (mul scalar rightAddend) := by
  intro scalar leftAddend rightAddend
  cases scalar <;> cases leftAddend <;> cases rightAddend <;> rfl

/-- Right distributivity of strategy meet over join. -/
theorem mul_distrib_right : ∀ leftAddend rightAddend scalar,
    mul (add leftAddend rightAddend) scalar =
      add (mul leftAddend scalar) (mul rightAddend scalar) := by
  intro leftAddend rightAddend scalar
  cases leftAddend <;> cases rightAddend <;> cases scalar <;> rfl

/-- Stack annihilates on the left. -/
theorem mul_zero_left : ∀ value, mul .stack value = .stack := by
  intro value
  cases value <;> rfl

/-- Stack annihilates on the right. -/
theorem mul_zero_right : ∀ value, mul value .stack = .stack := by
  intro value
  cases value <;> rfl

/-- Strategy subsumption is reflexive. -/
theorem le_refl : ∀ value, le value value := by
  intro value
  cases value <;> exact True.intro

/-- Strategy subsumption is transitive. -/
theorem le_trans : ∀ first second third,
    le first second → le second third → le first third := by
  intro first second third firstLeSecond secondLeThird
  cases first <;> cases second <;> cases third <;>
    first | exact True.intro | contradiction

/-- Strategy addition is monotone. -/
theorem add_mono : ∀ leftLow leftHigh rightLow rightHigh,
    le leftLow leftHigh → le rightLow rightHigh →
      le (add leftLow rightLow) (add leftHigh rightHigh) := by
  intro leftLow leftHigh rightLow rightHigh leftLeq rightLeq
  cases leftLow <;> cases leftHigh <;> cases rightLow <;> cases rightHigh <;>
    first | exact True.intro | contradiction

/-- Strategy multiplication is monotone. -/
theorem mul_mono : ∀ leftLow leftHigh rightLow rightHigh,
    le leftLow leftHigh → le rightLow rightHigh →
      le (mul leftLow rightLow) (mul leftHigh rightHigh) := by
  intro leftLow leftHigh rightLow rightHigh leftLeq rightLeq
  cases leftLow <;> cases leftHigh <;> cases rightLow <;> cases rightHigh <;>
    first | exact True.intro | contradiction

end AllocStrategy

/-! ## Space-grade product -/

/-- Space grade: allocation strategy paired with a byte bound. -/
structure SpaceGrade : Type where
  /-- Allocation strategy required by the value. -/
  strategy : AllocStrategy
  /-- Checked byte bound, finite or unbounded. -/
  byteBound : ComplexityGrade
  deriving DecidableEq, Repr

namespace SpaceGrade

/-- Parallel composition combines strategy permissions and byte bounds. -/
def add (first second : SpaceGrade) : SpaceGrade :=
  ⟨AllocStrategy.add first.strategy second.strategy,
    ComplexityGrade.add first.byteBound second.byteBound⟩

/-- Sequential composition scales strategy permissions and byte bounds. -/
def mul (first second : SpaceGrade) : SpaceGrade :=
  ⟨AllocStrategy.mul first.strategy second.strategy,
    ComplexityGrade.mul first.byteBound second.byteBound⟩

/-- Product preorder for strategy and byte-bound subsumption. -/
def le (first second : SpaceGrade) : Prop :=
  AllocStrategy.le first.strategy second.strategy ∧
    ComplexityGrade.le first.byteBound second.byteBound

/-- Extensional equality helper for `SpaceGrade`. -/
theorem ext_eq
    {first second : SpaceGrade}
    (strategyEq : first.strategy = second.strategy)
    (byteBoundEq : first.byteBound = second.byteBound) :
    first = second := by
  cases first with
  | mk firstStrategy firstByteBound =>
  cases second with
  | mk secondStrategy secondByteBound =>
  cases strategyEq
  cases byteBoundEq
  rfl

end SpaceGrade

/-- Space grades form the product semiring of allocation strategy and
bounded-or-unbounded byte counts. -/
instance : GradeSemiring SpaceGrade where
  zero := ⟨.stack, .bound 0⟩
  one  := ⟨.heap, .bound 1⟩
  add  := SpaceGrade.add
  mul  := SpaceGrade.mul
  le   := SpaceGrade.le

  add_assoc := by
    intro first second third
    exact SpaceGrade.ext_eq
      (AllocStrategy.add_assoc first.strategy second.strategy third.strategy)
      (ComplexityGrade.add_assoc first.byteBound second.byteBound third.byteBound)

  add_comm := by
    intro first second
    exact SpaceGrade.ext_eq
      (AllocStrategy.add_comm first.strategy second.strategy)
      (ComplexityGrade.add_comm first.byteBound second.byteBound)

  add_zero_left := by
    intro value
    exact SpaceGrade.ext_eq
      (AllocStrategy.add_zero_left value.strategy)
      (ComplexityGrade.add_zero_left value.byteBound)

  add_zero_right := by
    intro value
    exact SpaceGrade.ext_eq
      (AllocStrategy.add_zero_right value.strategy)
      (ComplexityGrade.add_zero_right value.byteBound)

  mul_assoc := by
    intro first second third
    exact SpaceGrade.ext_eq
      (AllocStrategy.mul_assoc first.strategy second.strategy third.strategy)
      (ComplexityGrade.mul_assoc first.byteBound second.byteBound third.byteBound)

  mul_one_left := by
    intro value
    exact SpaceGrade.ext_eq
      (AllocStrategy.mul_one_left value.strategy)
      (ComplexityGrade.mul_one_left value.byteBound)

  mul_one_right := by
    intro value
    exact SpaceGrade.ext_eq
      (AllocStrategy.mul_one_right value.strategy)
      (ComplexityGrade.mul_one_right value.byteBound)

  mul_distrib_left := by
    intro scalar leftAddend rightAddend
    exact SpaceGrade.ext_eq
      (AllocStrategy.mul_distrib_left
        scalar.strategy leftAddend.strategy rightAddend.strategy)
      (ComplexityGrade.mul_distrib_left
        scalar.byteBound leftAddend.byteBound rightAddend.byteBound)

  mul_distrib_right := by
    intro leftAddend rightAddend scalar
    exact SpaceGrade.ext_eq
      (AllocStrategy.mul_distrib_right
        leftAddend.strategy rightAddend.strategy scalar.strategy)
      (ComplexityGrade.mul_distrib_right
        leftAddend.byteBound rightAddend.byteBound scalar.byteBound)

  mul_zero_left := by
    intro value
    exact SpaceGrade.ext_eq
      (AllocStrategy.mul_zero_left value.strategy)
      (ComplexityGrade.mul_zero_left value.byteBound)

  mul_zero_right := by
    intro value
    exact SpaceGrade.ext_eq
      (AllocStrategy.mul_zero_right value.strategy)
      (ComplexityGrade.mul_zero_right value.byteBound)

  le_refl := by
    intro value
    exact And.intro
      (AllocStrategy.le_refl value.strategy)
      (ComplexityGrade.le_refl value.byteBound)

  le_trans := by
    intro first second third firstLeSecond secondLeThird
    exact And.intro
      (AllocStrategy.le_trans
        first.strategy second.strategy third.strategy
        firstLeSecond.left secondLeThird.left)
      (ComplexityGrade.le_trans
        first.byteBound second.byteBound third.byteBound
        firstLeSecond.right secondLeThird.right)

  add_mono := by
    intro leftLow leftHigh rightLow rightHigh leftLeq rightLeq
    exact And.intro
      (AllocStrategy.add_mono
        leftLow.strategy leftHigh.strategy rightLow.strategy rightHigh.strategy
        leftLeq.left rightLeq.left)
      (ComplexityGrade.add_mono
        leftLow.byteBound leftHigh.byteBound rightLow.byteBound rightHigh.byteBound
        leftLeq.right rightLeq.right)

  mul_mono := by
    intro leftLow leftHigh rightLow rightHigh leftLeq rightLeq
    exact And.intro
      (AllocStrategy.mul_mono
        leftLow.strategy leftHigh.strategy rightLow.strategy rightHigh.strategy
        leftLeq.left rightLeq.left)
      (ComplexityGrade.mul_mono
        leftLow.byteBound leftHigh.byteBound rightLow.byteBound rightHigh.byteBound
        leftLeq.right rightLeq.right)

/-! ## Smoke samples -/

/-- Stack plus heap allocation requires heap allocation. -/
example :
    SpaceGrade.add ⟨.stack, .bound 0⟩ ⟨.heap, .bound 7⟩ =
      ⟨.heap, .bound 7⟩ := rfl

/-- Stack allocation annihilates the strategy side of sequential space. -/
example :
    SpaceGrade.mul ⟨.stack, .bound 0⟩ ⟨.heap, .unbounded⟩ =
      ⟨.stack, .bound 0⟩ := rfl

/-- Region-bounded finite allocation fits under heap-unbounded allowance. -/
example :
    SpaceGrade.le ⟨.region, .bound 4⟩ ⟨.heap, .unbounded⟩ :=
  And.intro True.intro True.intro

end LeanFX2.Graded.Instances
