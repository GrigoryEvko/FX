import LeanFX2.Graded.Semiring

/-! # Graded/Instances/Usage — usage semiring `{0, 1, ω}`

The classical linear-logic semiring: 0 = unused, 1 = linear (exactly
once), ω = unrestricted (any number of uses).

## Element type

```lean
inductive UsageGrade
  | zero    -- absent / erased
  | one     -- linear (exactly once)
  | omega   -- unrestricted
```

## Operations (per fx_design.md §6.1)

### Addition (parallel use)

| `+` | 0 | 1 | ω |
|-----|---|---|---|
| 0   | 0 | 1 | ω |
| 1   | 1 | ω | ω |
| ω   | ω | ω | ω |

`1 + 1 = ω` is the key collision: a linear binding used in both
branches of an `if` accumulates to `ω`, which is illegal for a
linearly-typed binding → type error.

### Multiplication (sequential scaling)

| `*` | 0 | 1 | ω |
|-----|---|---|---|
| 0   | 0 | 0 | 0 |
| 1   | 0 | 1 | ω |
| ω   | 0 | ω | ω |

`0` annihilates.  `1` is identity.  `ω * x = x or ω` for non-zero.

### Order

`0 ≤ 1 ≤ ω`.  Subsumption: a value at grade 0 fits where 1 expected;
1 fits where ω expected.

## Surface mode mapping

Per fx_design.md §7:
* `own x` (default) → `1`
* `ref x` (shared borrow) → `ω` (read-only, replicable)
* `ref mut x` (exclusive) → `1` (one writer at a time)
* `affine x` → grade ≤ 1
* `@[copy]` on type → all bindings of that type at `ω`
* `ghost x` → `0` (compile-time only, erased)

## Wood-Atkey context division

For lambda rule's `Γ/p`:
* `1/ω = 0`  — linear variable in ω-closure becomes erased
* `1/1 = 1`
* `0/anything = 0`
* `ω/ω = ω`
* `ω/1 = ω`

The rejection of Atkey 2018's `fn(f) => fn(x) => f(f(x))` follows:
`f` has grade 1, the inner lambda has grade ω, so `f`'s available
grade in body is `1/ω = 0` → cannot use → type error.

## Dependencies

* `Graded/Semiring.lean`

## Downstream

* `Graded/Rules.lean` — usage semiring is the canonical instance
* All linear-tracking code

## Implementation plan (Phase 8)

1. Define `UsageGrade` inductive
2. Define add/mul/le tables
3. Prove all 11 semiring + preorder laws (each is finite case analysis)
4. Provide `instance : GradeSemiring UsageGrade`
5. `Decidable` instances for `=` and `≤`
6. Smoke: Atkey-2018 witness rejected via context division

Target: ~250 lines.
-/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-- The usage grade `{0, 1, ω}` per fx_design.md §6.1.  Three-element
inductive — non-indexed, so wildcards in `match` do not leak propext. -/
inductive UsageGrade : Type
  | zero    -- absent / erased
  | one     -- linear (exactly once)
  | omega   -- unrestricted
  deriving DecidableEq, Repr

namespace UsageGrade

/-- Parallel-use addition.  Fully enumerated 9-case table.  Note
`one + one = omega` — the key collision that rejects a linear binding
used in both branches of an `if`. -/
def add : UsageGrade → UsageGrade → UsageGrade
  | .zero,  rightOperand  => rightOperand
  | .one,   .zero          => .one
  | .one,   .one           => .omega
  | .one,   .omega         => .omega
  | .omega, _              => .omega

/-- Sequential scaling.  Fully enumerated 9-case table.  `0`
annihilates; `1` is identity; `ω * (non-zero) = ω`. -/
def mul : UsageGrade → UsageGrade → UsageGrade
  | .zero,  _              => .zero
  | .one,   rightOperand   => rightOperand
  | .omega, .zero          => .zero
  | .omega, .one           => .omega
  | .omega, .omega         => .omega

/-- Subsumption preorder `0 ≤ 1 ≤ ω`.  Smaller grade = more
restrictive (zero is most restrictive — the binding is unused). -/
def le : UsageGrade → UsageGrade → Prop
  | .zero,  _              => True
  | .one,   .zero          => False
  | .one,   .one           => True
  | .one,   .omega         => True
  | .omega, .zero          => False
  | .omega, .one           => False
  | .omega, .omega         => True

/-- Wood-Atkey context division `pi/p = max { d : d * p ≤ pi }`.
Used in the corrected Lam rule (Wood/Atkey 2022): when a binding at
grade `pi` is captured in a lambda whose grade is `p`, the binding's
available grade inside the closure body is `pi/p`.  Notable case:
`one / omega = zero` — a linear binding inside an unrestricted
closure is forced to grade zero, blocking the captured-and-reused
pattern that broke Atkey 2018's rule.

Encoded explicitly per fx_design.md §6.2; computed by full
enumeration since UsageGrade has only 9 ordered pairs. -/
def divides : UsageGrade → UsageGrade → UsageGrade
  | _,      .zero  => .omega        -- `_ / 0 = ω` (degenerate; max grade)
  | .zero,  _      => .zero         -- `0 / _ = 0` (no grade can recover use)
  | .one,   .one   => .one          -- `1 / 1 = 1`
  | .one,   .omega => .zero         -- `1 / ω = 0` (linear in unrestricted closure → erased)
  | .omega, .one   => .omega        -- `ω / 1 = ω`
  | .omega, .omega => .omega        -- `ω / ω = ω`

end UsageGrade

/-- The usage `{0, 1, ω}` semiring.  All 17 algebra/preorder laws
discharged by full case enumeration (3, 9, or 27 sub-cases each) over
the non-indexed inductive — no `decide`, no tactics that risk axiom
emission. -/
instance : GradeSemiring UsageGrade where
  zero := .zero
  one  := .one
  add  := UsageGrade.add
  mul  := UsageGrade.mul
  le   := UsageGrade.le

  add_assoc := fun first second third => match first, second, third with
    | .zero,  _,      _      => rfl
    | .one,   .zero,  _      => rfl
    | .one,   .one,   .zero  => rfl
    | .one,   .one,   .one   => rfl
    | .one,   .one,   .omega => rfl
    | .one,   .omega, _      => rfl
    | .omega, _,      _      => rfl

  add_comm := fun first second => match first, second with
    | .zero,  .zero  => rfl
    | .zero,  .one   => rfl
    | .zero,  .omega => rfl
    | .one,   .zero  => rfl
    | .one,   .one   => rfl
    | .one,   .omega => rfl
    | .omega, .zero  => rfl
    | .omega, .one   => rfl
    | .omega, .omega => rfl

  add_zero_left  := fun _ => rfl
  add_zero_right := fun value => match value with
    | .zero  => rfl
    | .one   => rfl
    | .omega => rfl

  mul_assoc := fun first second third => match first, second, third with
    | .zero,  _,      _      => rfl
    | .one,   _,      _      => rfl
    | .omega, .zero,  _      => rfl
    | .omega, .one,   _      => rfl
    | .omega, .omega, .zero  => rfl
    | .omega, .omega, .one   => rfl
    | .omega, .omega, .omega => rfl

  mul_one_left   := fun value => match value with
    | .zero  => rfl
    | .one   => rfl
    | .omega => rfl
  mul_one_right  := fun value => match value with
    | .zero  => rfl
    | .one   => rfl
    | .omega => rfl

  mul_distrib_left := fun scalar leftAddend rightAddend =>
    match scalar, leftAddend, rightAddend with
    | .zero,  _,      _      => rfl
    | .one,   _,      _      => rfl
    | .omega, .zero,  .zero  => rfl
    | .omega, .zero,  .one   => rfl
    | .omega, .zero,  .omega => rfl
    | .omega, .one,   .zero  => rfl
    | .omega, .one,   .one   => rfl
    | .omega, .one,   .omega => rfl
    | .omega, .omega, _      => rfl

  mul_distrib_right := fun leftAddend rightAddend scalar =>
    match leftAddend, rightAddend, scalar with
    | .zero,  .zero,  .zero  => rfl
    | .zero,  .zero,  .one   => rfl
    | .zero,  .zero,  .omega => rfl
    | .zero,  .one,   .zero  => rfl
    | .zero,  .one,   .one   => rfl
    | .zero,  .one,   .omega => rfl
    | .zero,  .omega, .zero  => rfl
    | .zero,  .omega, .one   => rfl
    | .zero,  .omega, .omega => rfl
    | .one,   .zero,  .zero  => rfl
    | .one,   .zero,  .one   => rfl
    | .one,   .zero,  .omega => rfl
    | .one,   .one,   .zero  => rfl
    | .one,   .one,   .one   => rfl
    | .one,   .one,   .omega => rfl
    | .one,   .omega, .zero  => rfl
    | .one,   .omega, .one   => rfl
    | .one,   .omega, .omega => rfl
    | .omega, .zero,  .zero  => rfl
    | .omega, .zero,  .one   => rfl
    | .omega, .zero,  .omega => rfl
    | .omega, .one,   .zero  => rfl
    | .omega, .one,   .one   => rfl
    | .omega, .one,   .omega => rfl
    | .omega, .omega, .zero  => rfl
    | .omega, .omega, .one   => rfl
    | .omega, .omega, .omega => rfl

  mul_zero_left  := fun _ => rfl
  mul_zero_right := fun value => match value with
    | .zero  => rfl
    | .one   => rfl
    | .omega => rfl

  le_refl := fun value => match value with
    | .zero  => True.intro
    | .one   => True.intro
    | .omega => True.intro

  le_trans := fun first second third firstLeSecond secondLeThird =>
    match first, second, third, firstLeSecond, secondLeThird with
    | .zero,  _,      _,      _, _ => True.intro
    | .one,   .one,   .one,   _, _ => True.intro
    | .one,   .one,   .omega, _, _ => True.intro
    | .one,   .omega, .omega, _, _ => True.intro
    | .omega, .omega, .omega, _, _ => True.intro

  add_mono := fun leftLow leftHigh rightLow rightHigh leftLeq rightLeq =>
    match leftLow, leftHigh, rightLow, rightHigh, leftLeq, rightLeq with
    -- leftLow = zero
    | .zero, .zero, .zero, .zero, _, _    => True.intro
    | .zero, .zero, .zero, .one, _, _     => True.intro
    | .zero, .zero, .zero, .omega, _, _   => True.intro
    | .zero, .zero, .one, .one, _, _      => True.intro
    | .zero, .zero, .one, .omega, _, _    => True.intro
    | .zero, .zero, .omega, .omega, _, _  => True.intro
    | .zero, .one, .zero, .zero, _, _     => True.intro
    | .zero, .one, .zero, .one, _, _      => True.intro
    | .zero, .one, .zero, .omega, _, _    => True.intro
    | .zero, .one, .one, .one, _, _       => True.intro
    | .zero, .one, .one, .omega, _, _     => True.intro
    | .zero, .one, .omega, .omega, _, _   => True.intro
    | .zero, .omega, .zero, .zero, _, _   => True.intro
    | .zero, .omega, .zero, .one, _, _    => True.intro
    | .zero, .omega, .zero, .omega, _, _  => True.intro
    | .zero, .omega, .one, .one, _, _     => True.intro
    | .zero, .omega, .one, .omega, _, _   => True.intro
    | .zero, .omega, .omega, .omega, _, _ => True.intro
    -- leftLow = one (so leftHigh ∈ {one, omega})
    | .one, .one, .zero, .zero, _, _      => True.intro
    | .one, .one, .zero, .one, _, _       => True.intro
    | .one, .one, .zero, .omega, _, _     => True.intro
    | .one, .one, .one, .one, _, _        => True.intro
    | .one, .one, .one, .omega, _, _      => True.intro
    | .one, .one, .omega, .omega, _, _    => True.intro
    | .one, .omega, .zero, .zero, _, _    => True.intro
    | .one, .omega, .zero, .one, _, _     => True.intro
    | .one, .omega, .zero, .omega, _, _   => True.intro
    | .one, .omega, .one, .one, _, _      => True.intro
    | .one, .omega, .one, .omega, _, _    => True.intro
    | .one, .omega, .omega, .omega, _, _  => True.intro
    -- leftLow = omega (so leftHigh = omega)
    | .omega, .omega, .zero, .zero, _, _  => True.intro
    | .omega, .omega, .zero, .one, _, _   => True.intro
    | .omega, .omega, .zero, .omega, _, _ => True.intro
    | .omega, .omega, .one, .one, _, _    => True.intro
    | .omega, .omega, .one, .omega, _, _  => True.intro
    | .omega, .omega, .omega, .omega, _, _ => True.intro

  mul_mono := fun leftLow leftHigh rightLow rightHigh leftLeq rightLeq =>
    match leftLow, leftHigh, rightLow, rightHigh, leftLeq, rightLeq with
    -- leftLow = zero (mul .zero _ = .zero, le .zero _ = True)
    | .zero, _, _, _, _, _ => True.intro
    -- leftLow = one, leftHigh ∈ {one, omega}
    | .one, .one, .zero, .zero, _, _      => True.intro
    | .one, .one, .zero, .one, _, _       => True.intro
    | .one, .one, .zero, .omega, _, _     => True.intro
    | .one, .one, .one, .one, _, _        => True.intro
    | .one, .one, .one, .omega, _, _      => True.intro
    | .one, .one, .omega, .omega, _, _    => True.intro
    | .one, .omega, .zero, .zero, _, _    => True.intro
    | .one, .omega, .zero, .one, _, _     => True.intro
    | .one, .omega, .zero, .omega, _, _   => True.intro
    | .one, .omega, .one, .one, _, _      => True.intro
    | .one, .omega, .one, .omega, _, _    => True.intro
    | .one, .omega, .omega, .omega, _, _  => True.intro
    -- leftLow = omega, leftHigh = omega
    | .omega, .omega, .zero, .zero, _, _  => True.intro
    | .omega, .omega, .zero, .one, _, _   => True.intro
    | .omega, .omega, .zero, .omega, _, _ => True.intro
    | .omega, .omega, .one, .one, _, _    => True.intro
    | .omega, .omega, .one, .omega, _, _  => True.intro
    | .omega, .omega, .omega, .omega, _, _ => True.intro

/-! ## Smoke: Wood-Atkey context-division correctness

Verifies the canonical entries that defeat Atkey 2018's broken Lam
rule.  These are the substantive checks; full division table is
algebraically straightforward. -/

example : UsageGrade.divides .one .omega = .zero := rfl
example : UsageGrade.divides .one .one = .one := rfl
example : UsageGrade.divides .omega .omega = .omega := rfl
example : UsageGrade.divides .zero .one = .zero := rfl

/-! ## Smoke: addition collision `1 + 1 = ω`

Verifies the canonical linearity violation: a linear binding used in
both branches accumulates to `ω`, which fails the linearity check
when the binding's declared grade was `1`. -/

example : UsageGrade.add .one .one = .omega := rfl

/-! ## Smoke: multiplication annihilation

`0 * x = 0` and `x * 0 = 0` — ghost computation on any value yields
ghost result, supporting the §6.1 `classified * 0 = 0` reasoning that
ghost computation on classified data leaks nothing. -/

example : UsageGrade.mul .zero .omega = .zero := rfl
example : UsageGrade.mul .omega .zero = .zero := rfl

end LeanFX2.Graded.Instances
