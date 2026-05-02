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

-- TODO Phase 8: UsageGrade inductive
-- TODO Phase 8: add/mul tables as match-based defs
-- TODO Phase 8: le as match-based def
-- TODO Phase 8: instance GradeSemiring UsageGrade with all laws

end LeanFX2.Graded.Instances
