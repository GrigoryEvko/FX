import LeanFX2.Graded.Semiring

/-! # Graded/Instances/Effect — effect lattice as semiring

Effects form a bounded join-semilattice — a degenerate semiring where
`+` and `*` are both join.

## Effect labels (per fx_design.md §9.4)

```lean
inductive EffectLabel
  | tot       -- pure terminating (zero)
  | div       -- may diverge
  | ghost     -- erased at runtime
  | exn       -- may raise
  | io        -- general input/output
  | alloc     -- may allocate heap
  | read      -- may read from references/state
  | write     -- may write (implies read)
  | async     -- may perform async operations
  | usrEffect (name : String)  -- user-defined effects
```

## EffectGrade as set

```lean
def EffectGrade : Type := Finset EffectLabel
```

(Or `List EffectLabel` with set-equivalence if Finset has propext
issues.)

## Operations

`+` = `*` = set union (lattice join).
* `Tot ∨ e = e`  (Tot is bottom = empty set)
* `e ∨ e = e` (idempotent)
* `e1 ∨ e2 = e2 ∨ e1` (commutative)

`0` = `Tot` (empty set).
`1` = `Tot` (also empty set — multiplicative identity).

`≤` = subset.  Subsumption: a `Tot` function fits where `IO`
expected, not vice versa.

## Per fx_design.md §B (Appendix B)

Only declared subeffect: `Read ⊆ Write`.  Other built-ins are
incomparable lattice elements.

```lean
def EffectLabel.le (e1 e2 : EffectLabel) : Prop :=
  e1 = e2 ∨ (e1 = Read ∧ e2 = Write)
```

(Then EffectGrade.le compares pointwise plus user-effect ordering.)

## Why a degenerate semiring works

For effect tracking, sequential and parallel composition both
*accumulate* effects (you don't multiply effect counts; you
union effect sets).  This means `+ = * = ∨`.  All semiring laws
hold trivially because join-semilattices satisfy them with both
ops being join.

## Dependencies

* `Graded/Semiring.lean`

## Downstream

* `Graded/Rules.lean` — effect grade tracks via App/Let rules
* fx_design.md §9 — full effect semantics

## Implementation plan (Phase 8)

1. Define `EffectLabel` enum + extension for user effects
2. Define `EffectGrade = Finset EffectLabel` (or List with set-equiv)
3. Define `+`, `*`, `≤` as join + subset
4. Discharge semiring laws (all trivial because of degenerate ops)
5. `instance : GradeSemiring EffectGrade`

Target: ~200 lines.
-/

namespace LeanFX2.Graded.Instances

-- TODO Phase 8: EffectLabel inductive
-- TODO Phase 8: EffectGrade as Finset/List
-- TODO Phase 8: GradeSemiring instance via degenerate (join) semiring

end LeanFX2.Graded.Instances
