import FX1Poly.Core.GeneratorCore

/-! # FX1Poly/Core/GeneratorCountPin — permanent stale-count guard

Docstrings and design notes keep citing stale generator counts (74, 188,
194 have all appeared); the enum currently has 198 constructors.  This
file pins the count as TWO theorems that break on ANY change to the
enum's size, forcing the pin (and every count-citing docstring it
guards) to be updated in the same change:

  * appending a 199th generator breaks `generatorCount_upperBound`
    (the new constructor's index is 198);
  * removing or reordering past `gen_npComplete` breaks
    `generatorCount_lastIndex`.

Together with constructor-index injectivity (by construction for an
enum) the two theorems pin the count at exactly `generatorCount`.

## Zero-axiom verification

`rfl` + `of_decide_eq_true rfl` per constructor — no `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
-/

namespace FX1Poly.Core

/-- The number of generators in the table.  UPDATE THIS PIN (and every
docstring citing the count) when the enum changes — the two theorems
below break on any size change. -/
def generatorCount : Nat := 198

/-- The LAST generator's constructor index attains `generatorCount - 1`:
the count from below. -/
theorem generatorCount_lastIndex :
    Generator.ctorIdx .gen_npComplete = generatorCount - 1 := rfl

/-- Every generator's constructor index is below `generatorCount`: the
count from above.  A 199th generator breaks this theorem. -/
theorem generatorCount_upperBound :
    ∀ generator : Generator,
      Generator.ctorIdx generator < generatorCount := by
  intro generator
  cases generator <;> exact of_decide_eq_true rfl

end FX1Poly.Core
