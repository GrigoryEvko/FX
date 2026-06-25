import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.RuleTables.CellTemplate

/-! # FX1PolyAudit/.../CellTemplate — the zero-axiom gate for the CellTemplate DSL data (SR-DSL-0a)

The closed CellTemplate DSL (the typing-side twin of ReductTemplate) + the structural well-formedness Bool fold.
The fold must be propext-clean: full-enumeration mutual structural recursion over CellTemplate/CellTemplateSpine,
`&&` + `Nat.blt`, no `deriving`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.ChildRef.isInRange
#assert_no_axioms FX1Poly.Typed.ReBasingMacro.refsInRange
#assert_no_axioms FX1Poly.Typed.CellTemplate.isWellFormed
#assert_no_axioms FX1Poly.Typed.CellTemplateSpine.allWellFormed

end FX1PolyAudit
