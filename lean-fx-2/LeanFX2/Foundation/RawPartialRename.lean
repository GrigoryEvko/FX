import LeanFX2.Foundation.RawPartialRename.Helpers
import LeanFX2.Foundation.RawPartialRename.Function
import LeanFX2.Foundation.RawPartialRename.VarLemmas
import LeanFX2.Foundation.RawPartialRename.Inversion
import LeanFX2.Foundation.RawPartialRename.UnweakenInversion

/-! # LeanFX2.Foundation.RawPartialRename — partial renaming (shim)

Partial raw renamings are the safe primitive for recognizing whether a
raw term is the weakening of a term in the previous outer scope.  A
naive `dropNewest?` recursion is wrong under binders: inside `lam` or
`pathLam`, index 0 is the binder and must be preserved while the outer
dropped variable shifts to index 1.  `PartialRawRenaming.lift` encodes
exactly that de Bruijn behaviour.

Carved into five sub-modules along the natural pipeline `helpers →
function definition → leaf lemmas → giant inversion → headline
corollary`:

| Sub-module | Family |
| --- | --- |
| `Helpers` | `PartialRawRenaming` type + `lift` / `dropNewest` + `Option.mapTwo` / `mapThree` |
| `Function` | `RawTerm.partialRename?` big def + `unweaken?` + `constantPathBody?` |
| `VarLemmas` | Variable, binder, and `pathLam` guardrail lemmas plus `partialRename?_rename_some` and `unweaken?_weaken` |
| `Inversion` | `Option.mapN_eq_some` decomposers, `lift_renamingInjectsBack`, and the giant per-constructor `partialRename?_imp_rename` induction |
| `UnweakenInversion` | `dropNewest_renamingInjectsBack` + `unweaken?_imp_weaken` headline corollary |

## Root status

Kernel infrastructure for the `Step.transpReflBeta` cd cascade; no
axioms. -/
