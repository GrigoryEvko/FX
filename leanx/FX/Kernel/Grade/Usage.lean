import FX.Kernel.Grade.Tier

/-!
# Usage (dimension 3) — `{0, 1, omega}` semiring

Per `fx_design.md` §6.1 and §6.3 (dim 3).  Tier S.  The central
grade dimension: tracks how many times a binding is consumed.

  * `zero`  — absent / erased / ghost; no runtime representation.
  * `one`   — linear; consumed exactly once.
  * `omega` — unrestricted; consumed any number of times.

## Surface-syntax mapping

Per `fx_design.md` §6.3 dim 3 and Appendix C (Mode Semiring):

  * `ghost`   → `zero`   (erased; no runtime occurrence)
  * (default) → `one`    (linear; exactly once)
  * `own x`   → `one`    (ownership; exactly once)
  * `ref mut` → `one`    (exclusive borrow; exactly-once-active)
  * `ref`     → `omega`  (shared borrow; duplicable)
  * `@[copy]` → `omega`  (unrestricted at the type level)
  * `affine`  → bound `≤ one` (zero or one use; drop allowed)

`affine` is a subsumption bound, not a carrier element — every
concrete grade is one of `{0, 1, omega}`; affine-ness is the
predicate "grade ≤ one".  The `LessEq` relation below captures it.

## §6.4 permission PCM (deferred)

`fx_design.md` §6.4 describes a finer fractional permission PCM
with `Frac(p) | Zero | Omega` where `p ∈ (0, 1]`.  Phase 1 uses
the coarse three-element quotient.  The collapse `Frac(1) ↦ one`,
`Frac(p<1) ↦ omega`, `Zero ↦ zero` is the standard "merge all
shared borrows" abstraction — sound for typing but it loses
fractional-permission precision.  A future Phase can refine the
carrier; the kernel interface does not change.

## Order choice

We use the **total order** `0 ≤ 1 ≤ omega` rather than Atkey 2018's
`refl + leOmega` partial order.  Both choices are sound.  The
total order is what Idris 2, Granule, and Linear Haskell pick,
and it makes Wood-Atkey context division (`Usage.div`) a total
function — necessary for the Pi-introduction rule.

Soundness of the total order:  the rule `0 ≤ 1` lets a ghost
binding be used where a linear one is demanded, but at the
value level there is nothing to use (`zero` erases), so the
demand is vacuously satisfied.  Linearity is still enforced by
the grade arithmetic:  `add one zero = one`, not zero, so
forgetting to consume a linear binding still produces a
grade-one residual that fails the exit check.

## Appendix H.8 realization

This file realizes the Tier-S entries of `Grade-semiring-laws`,
`Grade-division`, and `Grade-zero` for the Usage dimension.
None of those are `axiom` declarations in Lean; they are all
provable theorems over the three-element finite set.

## TierSComm instance

The `instance : TierSComm Usage` at the bottom of this file
binds the per-dim theorems above to the abstract tier class
methods (T2).  This formalises Usage's membership in the
commutative-semiring tier at the type level — see
`FX/Kernel/Grade/Tier.lean` for the class hierarchy.
-/

namespace FX.Kernel

/--
The usage semiring `{0, 1, omega}` from `fx_design.md` §6.1.
-/
inductive Usage : Type where
  | zero  : Usage
  | one   : Usage
  | omega : Usage
  deriving DecidableEq, Repr

namespace Usage

/-- Parallel use (addition).  `1 + 1 = omega` is the key rule:
    using a linear binding twice in parallel (e.g., both
    branches of an `if`) promotes its grade to unrestricted,
    which is rejected at the exit check for a linear binding. -/
def add : Usage → Usage → Usage
  | zero,  right => right
  | left,  zero  => left
  | one,   one   => omega
  | one,   omega => omega
  | omega, one   => omega
  | omega, omega => omega

/-- Sequential / scaled use (multiplication).  `zero` is the
    annihilator — scaling by an unused parameter erases the
    argument's usage entirely.  `one` is the identity. -/
def mul : Usage → Usage → Usage
  | zero,  _     => zero
  | _,     zero  => zero
  | one,   right => right
  | left,  one   => left
  | omega, omega => omega

/-- Lattice join (`max` in the total order `0 ≤ 1 ≤ omega`).

Used for the **branch-arm** semantics of `match` / `indRec` /
`if`: only one arm executes at runtime, so a binding used once
in each arm is used once in total, not twice.  This is the
difference between the Usage semiring's `add` (parallel
composition — both sides execute) and `join` (branch
selection — only one executes).

  * join zero x    = x         (bottom absorbs on the left)
  * join x zero    = x
  * join one one   = one       (same usage in both arms)
  * join one omega = omega
  * join omega _   = omega     (top absorbs)
-/
def join : Usage → Usage → Usage
  | zero,  right => right
  | left,  zero  => left
  | one,   one   => one
  | one,   omega => omega
  | omega, one   => omega
  | omega, omega => omega

/--
Subusage as the total chain `0 ≤ 1 ≤ omega`.

  * `refl x`      — every grade is `≤` itself.
  * `zeroLe x`    — `zero` is the bottom.
  * `leOmega x`   — `omega` is the top.

The three constructors together enumerate the reflexive,
transitive closure of `zero ≤ one ≤ omega` (with `refl` making
it reflexive on the middle element).
-/
inductive LessEq : Usage → Usage → Prop where
  | refl    : ∀ usage, LessEq usage usage
  | zeroLe  : ∀ usage, LessEq zero usage
  | leOmega : ∀ usage, LessEq usage omega

instance : LE Usage := ⟨LessEq⟩

/--
Wood-Atkey 2022 context division: `div x y` is the greatest
grade `d` such that `mul d y ≤ x`.  Used by the Pi-intro rule
to divide the ambient context by the lambda's grade.

The critical case is `div one omega = zero`: a linear binding
captured into an unrestricted closure becomes *erased* in the
closure's context, blocking Atkey 2018's Lam bug (see
`fx_design.md` §27.1).
-/
def div : Usage → Usage → Usage
  | _,         zero  => omega      -- d · 0 ≤ x holds for all d
  | numerator, one   => numerator  -- d · 1 = d, so d ≤ x
  | zero,      omega => zero       -- only zero satisfies d · omega ≤ 0
  | one,       omega => zero       -- d · omega ≤ 1 requires d = 0
  | omega,     omega => omega      -- d · omega ≤ omega holds for all d

/-! ### Semiring laws -/

theorem add_comm (leftUsage rightUsage : Usage) :
    add leftUsage rightUsage = add rightUsage leftUsage := by
  cases leftUsage <;> cases rightUsage <;> rfl

theorem add_assoc (leftUsage middleUsage rightUsage : Usage) :
    add (add leftUsage middleUsage) rightUsage
      = add leftUsage (add middleUsage rightUsage) := by
  cases leftUsage <;> cases middleUsage <;> cases rightUsage <;> rfl

theorem zero_add (usage : Usage) : add zero usage = usage := by
  cases usage <;> rfl

theorem add_zero (usage : Usage) : add usage zero = usage := by
  cases usage <;> rfl

theorem mul_assoc (leftUsage middleUsage rightUsage : Usage) :
    mul (mul leftUsage middleUsage) rightUsage
      = mul leftUsage (mul middleUsage rightUsage) := by
  cases leftUsage <;> cases middleUsage <;> cases rightUsage <;> rfl

/-- Usage mul is commutative.  Case analysis on the 3×3 element
    pairs from `{zero, one, omega}` — every pair's product
    equals the swapped pair's product by the table in `mul`'s
    definition.  Used by the aggregate
    `Grade.mul_comm_of_same_provenance` (Q48) together with the
    matching `Trust.mul_comm` and `Mutation.mul_comm`. -/
theorem mul_comm (leftUsage rightUsage : Usage) :
    mul leftUsage rightUsage = mul rightUsage leftUsage := by
  cases leftUsage <;> cases rightUsage <;> rfl

theorem zero_mul (usage : Usage) : mul zero usage = zero := by
  cases usage <;> rfl

theorem mul_zero (usage : Usage) : mul usage zero = zero := by
  cases usage <;> rfl

theorem one_mul (usage : Usage) : mul one usage = usage := by
  cases usage <;> rfl

theorem mul_one (usage : Usage) : mul usage one = usage := by
  cases usage <;> rfl

theorem left_distrib (scaleUsage leftUsage rightUsage : Usage) :
    mul scaleUsage (add leftUsage rightUsage)
      = add (mul scaleUsage leftUsage) (mul scaleUsage rightUsage) := by
  cases scaleUsage <;> cases leftUsage <;> cases rightUsage <;> rfl

theorem right_distrib (leftUsage rightUsage scaleUsage : Usage) :
    mul (add leftUsage rightUsage) scaleUsage
      = add (mul leftUsage scaleUsage) (mul rightUsage scaleUsage) := by
  cases leftUsage <;> cases rightUsage <;> cases scaleUsage <;> rfl

/-! ### Subusage laws -/

/-- Transitivity.  With the `refl` constructor this gives a preorder.
    Antisymmetry holds on the three-element carrier (`≤` is a
    partial order), but we do not need it for the kernel. -/
theorem LessEq.trans {leftUsage middleUsage rightUsage : Usage}
    (hLeftLeMiddle : leftUsage ≤ middleUsage)
    (hMiddleLeRight : middleUsage ≤ rightUsage) : leftUsage ≤ rightUsage := by
  cases hLeftLeMiddle with
  | refl    => exact hMiddleLeRight
  | zeroLe  =>
    cases hMiddleLeRight with
    | refl    => exact LessEq.zeroLe _
    | zeroLe  => exact LessEq.zeroLe _
    | leOmega => exact LessEq.zeroLe _
  | leOmega =>
    cases hMiddleLeRight with
    | refl    => exact LessEq.leOmega _
    | leOmega => exact LessEq.leOmega _
    -- note: the `zeroLe` case is impossible — `zeroLe` produces
    -- `LessEq zero _`, but `hMiddleLeRight : LessEq omega _` has `middleUsage = omega`.

/-- Decidability of subusage.  Usage has three elements so every
    pair is decidable by enumeration. -/
instance decLe : (leftUsage rightUsage : Usage) → Decidable (LessEq leftUsage rightUsage)
  | zero,  zero  => isTrue (LessEq.refl _)
  | zero,  one   => isTrue (LessEq.zeroLe _)
  | zero,  omega => isTrue (LessEq.zeroLe _)
  | one,   zero  => isFalse (fun hLe => by cases hLe)
  | one,   one   => isTrue (LessEq.refl _)
  | one,   omega => isTrue (LessEq.leOmega _)
  | omega, zero  => isFalse (fun hLe => by cases hLe)
  | omega, one   => isFalse (fun hLe => by cases hLe)
  | omega, omega => isTrue (LessEq.refl _)

/-! ### Wood-Atkey division — universal property -/

/-- `(div x y) * y ≤ x`: the product is bounded by the numerator.
    Combined with `div_universal`, this characterizes `div` as the
    greatest such `d`. -/
theorem div_mul_le (numerator denominator : Usage) :
    mul (div numerator denominator) denominator ≤ numerator := by
  cases numerator <;> cases denominator
  all_goals first
    | exact LessEq.refl _
    | exact LessEq.zeroLe _
    | exact LessEq.leOmega _

/-- Maximality: any `d` with `d * y ≤ x` is `≤ div x y`. -/
theorem div_universal (numerator denominator candidate : Usage)
    (hBound : mul candidate denominator ≤ numerator) :
    candidate ≤ div numerator denominator := by
  cases numerator <;> cases denominator <;> cases candidate
  all_goals first
    | exact LessEq.refl _
    | exact LessEq.zeroLe _
    | exact LessEq.leOmega _
    | (cases hBound)

/-! ### Further laws over the finite carrier -/

/-- Antisymmetry of `LessEq`.  On the three-element total order this
    is immediate; together with `refl` and `trans` it makes
    `{0, 1, omega}` a genuine partial (in fact total) order. -/
theorem LessEq.antisymm {leftUsage rightUsage : Usage}
    (hLeftLeRight : leftUsage ≤ rightUsage)
    (hRightLeLeft : rightUsage ≤ leftUsage) : leftUsage = rightUsage := by
  cases hLeftLeRight with
  | refl    => rfl
  | zeroLe  =>
    cases hRightLeLeft with
    | refl    => rfl
    | zeroLe  => rfl
  | leOmega =>
    cases hRightLeLeft with
    | refl    => rfl
    | leOmega => rfl

/-- `add` is monotone in the first argument (and by commutativity,
    in both). -/
theorem add_mono_left {smallerLeft largerLeft : Usage} (rightUsage : Usage)
    (hLeftLe : smallerLeft ≤ largerLeft) :
    add smallerLeft rightUsage ≤ add largerLeft rightUsage := by
  cases smallerLeft <;> cases largerLeft <;> cases rightUsage <;>
    first
      | exact LessEq.refl _
      | exact LessEq.zeroLe _
      | exact LessEq.leOmega _
      | (cases hLeftLe)

/-- `mul` is monotone in the first argument. -/
theorem mul_mono_left {smallerLeft largerLeft : Usage} (rightUsage : Usage)
    (hLeftLe : smallerLeft ≤ largerLeft) :
    mul smallerLeft rightUsage ≤ mul largerLeft rightUsage := by
  cases smallerLeft <;> cases largerLeft <;> cases rightUsage <;>
    first
      | exact LessEq.refl _
      | exact LessEq.zeroLe _
      | exact LessEq.leOmega _
      | (cases hLeftLe)

/-- Idempotence of `add` holds at the two absorbing elements —
    `one + one = omega`, so `one` is the exception.  This is the
    key fact that catches double-use of a linear binding across
    parallel branches. -/
theorem add_idem_zero : add zero zero = zero := rfl
theorem add_idem_omega : add omega omega = omega := rfl
theorem add_one_one_ne : add one one ≠ one := by decide

/-- Idempotence of `mul` holds at every element — `mul` is a
    monoid with idempotent top and bottom. -/
theorem mul_idem (usage : Usage) : mul usage usage = usage := by
  cases usage <;> rfl

end Usage

/-! ## TierSRing instance (T2 — strict semiring)

Usage is the ONE spec-§6.3 Tier-S dim that satisfies the strict
commutative-semiring laws per §6.1 (Appendix H.8): distinct `+`
and `*` tables, genuine `0 * x = 0` annihilation.  It is
therefore instanced at the TIGHTEST tier class: `TierSRing`.

Extension chain: `TierSRing ⊂ TierSComm ⊂ TierS ⊂ GradeCarrier`.
This single instance transparently provides the weaker classes
too — tier-generic theorems that quantify over `TierSComm` or
`TierS` automatically apply to Usage.

The audit (T6a) established that the other 14 spec-Tier-S dims
do NOT satisfy the strict annihilation law.  Their instances
live at `TierSIdem` (7 join-lattice dims), `TierSComm` (4
nat-arithmetic dims), or `TierS` (Provenance — non-commutative).
Lifetime cannot instance any Tier-S class because its kernel
has no additive unit. -/
instance : TierSRing Usage where
  default       := Usage.one
  le            := Usage.LessEq
  le_refl       := Usage.LessEq.refl
  le_trans      := Usage.LessEq.trans
  add           := Usage.add
  mul           := Usage.mul
  zero          := Usage.zero
  one           := Usage.one
  add_comm      := Usage.add_comm
  add_assoc     := Usage.add_assoc
  add_zero      := Usage.add_zero
  zero_add      := Usage.zero_add
  mul_assoc     := Usage.mul_assoc
  one_mul       := Usage.one_mul
  mul_one       := Usage.mul_one
  left_distrib  := Usage.left_distrib
  right_distrib := Usage.right_distrib
  zero_mul      := Usage.zero_mul
  mul_zero      := Usage.mul_zero
  mul_comm      := Usage.mul_comm

end FX.Kernel
