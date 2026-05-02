import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Mode

/-! # Context — typing environments.

`Ctx mode level scope` is the typing context: a list of `Ty level k` values
for `k = 0, 1, ..., scope-1`, paired with a fixed `Mode` for the whole context.

## Constructors

* `Ctx.empty : Ctx mode level 0`
* `Ctx.cons : Ctx mode level scope → Ty level scope → Ctx mode level (scope+1)`

## Operations

* `varType : Ctx mode level scope → Fin scope → Ty level scope`
  — looks up the type at position `i`, weakened to the full scope size

## Mode discipline

A whole `Ctx` carries a single `Mode`.  Modal effects (e.g., `ghost x`)
are encoded at the **Ty** level (`Ty.modal`), not the context level — cleaner
than per-binding mode tags.

## Dependencies

* `Foundation/Ty.lean` — context entries are Ty values
* `Foundation/Mode.lean` — context-level mode parameter

## Downstream

* `Term.lean` — first index is `Ctx`
* `Graded/Ctx.lean` — graded contexts extend `Ctx` with GradeVector per binding
-/

namespace LeanFX2

-- TODO: Ctx inductive
-- TODO: varType (with weaken stack)

end LeanFX2
