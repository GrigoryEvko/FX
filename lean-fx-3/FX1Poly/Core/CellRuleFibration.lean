import FX1Poly.Tier0.RuleFibration
import FX1Poly.Tier0.Term.Cell.CellSort
import FX1Poly.Tier0.Term.Generator.GeneratorCore

/-! # FX1Poly/Core/CellRuleFibration — the cell-rule fibration over the seven sorts

The Tier0 `RuleFibration` instantiated at the kernel's own axes and heads: the AXES are the seven
`CellSort`s (`context · type · term · mode · effect · grade · protocol` — the fibration strata a
`PolyCell` lives in) and the HEADS are the `Generator`s.  A `CellRuleBundle payload` is then exactly
"for each fibration axis, the per-generator rules at that axis" — the static-side, sort-generic
companion of the dim-1 `RuleTableBundle`.

The generic lookup / inhabitation / orthogonality machinery comes for free from Tier0; the typed
layer wires the `.type` axis to the typing-row lookup, and the remaining axes wire their own rule
tables in by the same shape.

Zero-axiom: a single `abbrev`.  No new definitions beyond the instantiation — all content is the
Tier0 substrate. -/

namespace FX1Poly.Core

open FX1Poly.Tier0 (RuleFibration)

/-- ★ **The cell-rule fibration** — the Tier0 `RuleFibration` at the seven `CellSort` axes and the
`Generator` heads.  `bundle.rowsAt sort generator` is the rules a generator fires at fibration axis
`sort`; `bundle.inhabits`, `bundle.isOrthogonalAt`, `bundle.isOrthogonalOverAt` are the inherited
decidable cell operations. -/
abbrev CellRuleBundle (payload : CellSort → Type) := RuleFibration CellSort Generator payload

end FX1Poly.Core
