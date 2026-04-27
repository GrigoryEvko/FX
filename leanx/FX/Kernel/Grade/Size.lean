import FX.Kernel.Grade.Tier

/-!
# Size (dimension 20) — codata observation depth

Per `fx_design.md` §6.3 (dim 20) and §3.5 (codata types).
Every codata value carries a size parameter `s : size`
bounding the depth at which observations (destructor
applications) may proceed.  A `stream<s>(a)` can be observed
`s` times; each destructor call consumes one size unit.

  * `finite n`    — observation depth at most `n`; shrinks by
                    one per destructor call.
  * `omega`       — unbounded depth.  Productive codata at the
                    full infinite horizon.

## Surface-syntax mapping

Per §3.5 and §6.3 dim 20 the grant is:

  * `sized s;` clause          → `s` (binder, resolved per call site)
  * `sized s; with Productive` → `omega` (productive infinite
                                           observation permitted)

## Algebra

Parallel combine (`add`) is `max` — when two observation paths
meet (branches of an `if` over codata), the joined observation
depth is the max of the two.  Sequential combine (`mul`) is
`add` — chaining observations through a fold adds their depths,
which in `omega+Nat` arithmetic is still `omega` when either
operand is `omega`.

  * add (finite n) (finite m) = finite (Nat.max n m)   (parallel)
  * add omega _                = omega
  * add _ omega                = omega

  * mul (finite n) (finite m) = finite (n + m)         (sequential)
  * mul omega _                = omega
  * mul _ omega                = omega

The preorder: `finite n ≤ finite m` iff `n ≤ m`;
`finite _ ≤ omega`; `omega ≤ omega`.  `finite 0` is the bottom
(fully-observed / no remaining budget), `omega` is the top.

Distributivity is not a clean semiring law because `mul` is
addition (not multiplication), but the Tier-S kernel dispatch
uses only `add`/`mul` separately and the `LessEq` monotonicity.
-/

namespace FX.Kernel

/-- The size grade — a codata observation-depth budget.
    `finite n` for bounded budgets; `omega` for productive
    infinite. -/
inductive Size : Type where
  | finite : Nat → Size
  | omega  : Size
  deriving DecidableEq, Repr

namespace Size

/-- Parallel combine — worst-case depth across branches is the
    max.  `omega` absorbs. -/
def add : Size → Size → Size
  | finite leftDepth, finite rightDepth => finite (Nat.max leftDepth rightDepth)
  | omega,            _                  => omega
  | _,                omega              => omega

/-- Sequential combine — observation depths chain additively,
    with `omega` absorbing. -/
def mul : Size → Size → Size
  | finite leftDepth, finite rightDepth => finite (leftDepth + rightDepth)
  | omega,            _                  => omega
  | _,                omega              => omega

/-! ## Subsumption

A smaller observation depth sits under a larger one — a
codata fragment observed at depth 3 is also observable at
depth 5, depth omega, etc.  `finite 0` is the bottom of the
preorder; `omega` is the top.
-/
inductive LessEq : Size → Size → Prop where
  | finiteLe : ∀ {leftDepth rightDepth}, leftDepth ≤ rightDepth →
                 LessEq (finite leftDepth) (finite rightDepth)
  | finiteLeOmega : ∀ n, LessEq (finite n) omega
  | omegaRefl    : LessEq omega omega

instance : LE Size := ⟨LessEq⟩

theorem LessEq.refl (size : Size) : size ≤ size := by
  cases size with
  | finite n => exact LessEq.finiteLe (Nat.le_refl n)
  | omega    => exact LessEq.omegaRefl

theorem LessEq.trans {lowerSize middleSize upperSize : Size}
    (lowerLeMiddle : lowerSize ≤ middleSize)
    (middleLeUpper : middleSize ≤ upperSize) :
    lowerSize ≤ upperSize := by
  cases lowerLeMiddle with
  | finiteLe lowerLe =>
    cases middleLeUpper with
    | finiteLe middleLe =>
      exact LessEq.finiteLe (Nat.le_trans lowerLe middleLe)
    | finiteLeOmega _ =>
      exact LessEq.finiteLeOmega _
  | finiteLeOmega _ =>
    cases middleLeUpper with
    | omegaRefl => exact LessEq.finiteLeOmega _
  | omegaRefl =>
    exact middleLeUpper

instance decLe : (leftSize rightSize : Size) → Decidable (LessEq leftSize rightSize)
  | finite leftDepth, finite rightDepth =>
    if h : leftDepth ≤ rightDepth then
      isTrue (LessEq.finiteLe h)
    else
      isFalse (fun contra => by cases contra; contradiction)
  | finite _,         omega  => isTrue (LessEq.finiteLeOmega _)
  | omega,            finite _ =>
    isFalse (fun contra => by cases contra)
  | omega,            omega  => isTrue LessEq.omegaRefl

/-! ## Laws -/

theorem add_comm (leftSize rightSize : Size) :
    add leftSize rightSize = add rightSize leftSize := by
  cases leftSize <;> cases rightSize <;> simp [add, Nat.max_comm]

theorem add_assoc (leftSize middleSize rightSize : Size) :
    add (add leftSize middleSize) rightSize
      = add leftSize (add middleSize rightSize) := by
  cases leftSize <;> cases middleSize <;> cases rightSize <;> simp [add, Nat.max_assoc]

theorem finite_zero_add (size : Size) : add (finite 0) size = size := by
  cases size <;> simp [add, Nat.max]

theorem add_finite_zero (size : Size) : add size (finite 0) = size := by
  cases size <;> simp [add, Nat.max]

/-- Size mul is commutative — `finite`/`finite` falls back to
    `Nat.add_comm`; `omega` cases both yield `omega`. -/
theorem mul_comm (leftSize rightSize : Size) :
    mul leftSize rightSize = mul rightSize leftSize := by
  cases leftSize <;> cases rightSize <;> simp [mul, Nat.add_comm]

/-- Identity for mul is `finite 0`: `finite 0 * x = x` because
    `0 + n = n` and `omega` is absorbed. -/
theorem finite_zero_mul (size : Size) : mul (finite 0) size = size := by
  cases size <;> simp [mul]

theorem mul_finite_zero (size : Size) : mul size (finite 0) = size := by
  cases size <;> simp [mul]

/-- `omega` is the absorbing element for `add`. -/
theorem omega_add (size : Size) : add omega size = omega := rfl

theorem add_omega (size : Size) : add size omega = omega := by
  cases size <;> rfl

theorem mul_assoc (leftSize middleSize rightSize : Size) :
    mul (mul leftSize middleSize) rightSize
      = mul leftSize (mul middleSize rightSize) := by
  cases leftSize <;> cases middleSize <;> cases rightSize <;> simp [mul, Nat.add_assoc]

/-- `omega` absorbs `mul` too. -/
theorem omega_mul (size : Size) : mul omega size = omega := rfl
theorem mul_omega (size : Size) : mul size omega = omega := by
  cases size <;> rfl

/-- `omega` is the top of the preorder. -/
theorem le_omega (size : Size) : size ≤ omega := by
  cases size with
  | finite _ => exact LessEq.finiteLeOmega _
  | omega    => exact LessEq.omegaRefl

/-- `finite 0` is the bottom of the preorder. -/
theorem finite_zero_le (size : Size) : finite 0 ≤ size := by
  cases size with
  | finite n => exact LessEq.finiteLe (Nat.zero_le n)
  | omega    => exact LessEq.finiteLeOmega _

end Size

/-! ## TierSComm instance (T2)

Size uses asymmetric operations: `add := max` (parallel observations
take the worst-case depth), `mul := Nat.+` (sequential observations
accumulate).  Both share `finite 0` as identity (`max 0 n = n`,
`0 + n = n`), and `omega` as the absorbing top.

Unlike the 7 `TierSIdem` dims, `add ≠ mul` here — max vs add.  So
Size does NOT fit `TierSIdem`.  It instances `TierSComm` (both are
commutative: max via `Nat.max_comm`, add via `Nat.add_comm`). -/
instance : TierSComm Size where
  default      := Size.finite 0
  le           := Size.LessEq
  le_refl      := Size.LessEq.refl
  le_trans     := Size.LessEq.trans
  add          := Size.add
  mul          := Size.mul
  zero         := Size.finite 0
  add_comm     := Size.add_comm
  add_assoc    := Size.add_assoc
  add_zero     := Size.add_finite_zero
  zero_add     := Size.finite_zero_add
  mul_assoc    := Size.mul_assoc
  mul_comm     := Size.mul_comm

end FX.Kernel
