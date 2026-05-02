import LeanFX2.Graded.Semiring

/-! # Graded/Instances/Security — security lattice `unclassified ≤ classified`

Two-element lattice for information-flow tracking.

## Element type

```lean
inductive SecurityGrade
  | unclassified
  | classified
```

## Operations (per fx_design.md §6.1)

### Addition (combining)

`+` is join (lattice union):
* `u + u = u`
* `u + c = c`
* `c + c = c`

Mixing public and secret yields secret.

### Multiplication

`*` is also join for non-zero grades:
* `c * 0 = 0` (ghost computation on secret erased — leaks nothing)
* `c * 1 = c`
* `c * c = c`

The annihilation `c * 0 = 0` is the principle: a ghost computation
(grade 0 in usage dim) doesn't actually run, so its security label
is irrelevant.  Compiler can erase the secret data structure.

## Subsumption (no implicit downgrade)

`unclassified ≤ classified`.  Subsumption only goes ONE direction:
a value of grade `unclassified` fits where `classified` expected
(safe — public data can be treated as if it were secret).
The reverse is NOT allowed without `declassify` (controlled
information flow).

## Implicit flows tracked

Per fx_design.md §12.2: even branching on a secret value taints
control flow.  This is captured by the rule structure, not the
semiring — the App/If rules combine grades from scrutinee and
branches such that branching on secret-graded scrutinee makes
the result secret-graded too.

## Dependencies

* `Graded/Semiring.lean`

## Downstream

* `Graded/Rules.lean` — security grade tracked via App/Let/If rules
* fx_design.md §12 — full IFC semantics
* CT effect (constant-time execution) — secret-graded values cannot
  appear in If/array-index positions

## Implementation plan (Phase 8)

1. Define `SecurityGrade` inductive
2. Define `+, *, ≤` tables
3. Discharge laws (4 cases each)
4. `instance : GradeSemiring SecurityGrade`
5. `Decidable` instances

Target: ~120 lines.
-/

namespace LeanFX2.Graded.Instances

-- TODO Phase 8: SecurityGrade inductive
-- TODO Phase 8: add/mul/le tables
-- TODO Phase 8: GradeSemiring instance

end LeanFX2.Graded.Instances
