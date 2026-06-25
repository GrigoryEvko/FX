import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.RuleTables.CellTemplateInterpretAdequacy

/-! # FX1PolyAudit/.../CellTemplateInterpretAdequacy — the zero-axiom gate for the SR-DSL-0c down-payment

Per-declaration zero-axiom gate for the three `rfl`-faithfulness validations (`interpret?` reproduces the shipped
`appElimRule.outputType`, the `natElim` succ-branch classifier `natElimDependentSuccBranchType motive` via the
`macroReBasing` depth-peel at depth 2, and the `universeCodeCell level0 flag` formedness classifier via the
`universeCode` leaf).  Each is a pure `rfl`, so the gate confirms the whole interpreter reduces axiom-free on
concrete rows.  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.appOutputTemplate_adequate
#assert_no_axioms FX1Poly.Typed.natElimSuccBranchClassifierTemplate_adequate
#assert_no_axioms FX1Poly.Typed.universeFormednessClassifierTemplate_adequate

end FX1PolyAudit
