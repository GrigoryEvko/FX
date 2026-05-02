import LeanFX2.Graded.Rules
import LeanFX2.Graded.Instances.Usage

/-! # Smoke/Graded — Atkey-2018 witness rejection + canonical examples.

```lean
-- The Atkey-2018 unsoundness witness:
-- fn higher_order(f: i64 -> i64) : i64 -> i64 = fn(x) => f(f(x))
-- This SHOULD NOT typecheck under Wood/Atkey's corrected rule.
example : ¬ ∃ wellTypedTerm,
    Graded.WellTyped Γ (RawTerm.lam (RawTerm.lam
        (RawTerm.app (RawTerm.var 1) (RawTerm.app (RawTerm.var 1) (RawTerm.var 0)))))
        wellTypedTerm UsageGrade.one
  := by ...

-- Canonical linear example: fn(x) => x typechecks at grade 1
example : Graded.WellTyped Γ (RawTerm.lam (RawTerm.var 0)) ... UsageGrade.one := ...

-- Canonical unrestricted example: fn(x) => x typechecks at grade ω
example : Graded.WellTyped Γ (RawTerm.lam (RawTerm.var 0)) ... UsageGrade.omega := ...
```

## Dependencies

* `Graded/Rules.lean`, `Graded/Instances/Usage.lean`

## Implementation plan (Layer 14)

1. Atkey-2018 witness rejection
2. Canonical linear / affine / unrestricted examples
3. Effect grade examples (Tot, IO, IO+Async)
4. Security grade examples (unclassified flow / classified flow)
-/

namespace LeanFX2.Smoke

-- TODO: graded smoke examples — including Atkey-2018 rejection

end LeanFX2.Smoke
