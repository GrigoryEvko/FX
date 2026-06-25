import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.RuleTables.CellTemplate

/-! # FX1PolyAudit/.../CellTemplate — the zero-axiom gate for the CellTemplate DSL + interpreter (SR-DSL-0a + 0b)

The closed CellTemplate DSL (the typing-side twin of ReductTemplate) + the structural well-formedness Bool fold
(SR-DSL-0a) + the `interpret?` depth-graded interpreter and its `resolve*`/`lmaxAll` helpers (SR-DSL-0b).  All
must be propext-clean: full-enumeration mutual structural recursion over CellTemplate/CellTemplateSpine and over
the `(depth, template)` / `(childShifts, spine)` interpreter arms, `Option` do-notation, `Nat.blt`, and the
`injectionHead` `if`-chain over `DecidableEq Generator` (elimRuleOf-style) — no `deriving`, no wildcard over the
200-constructor `Generator` enum. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.ChildRef.isInRange
#assert_no_axioms FX1Poly.Typed.ReBasingMacro.refsInRange
#assert_no_axioms FX1Poly.Typed.CellTemplate.isWellFormed
#assert_no_axioms FX1Poly.Typed.CellTemplateSpine.allWellFormed
#assert_no_axioms FX1Poly.Typed.lmaxAll
#assert_no_axioms FX1Poly.Typed.resolveChildRef?
#assert_no_axioms FX1Poly.Typed.resolveLevelSource
#assert_no_axioms FX1Poly.Typed.resolveFlagSource
#assert_no_axioms FX1Poly.Typed.CellTemplate.interpret?
#assert_no_axioms FX1Poly.Typed.interpretSpine?

end FX1PolyAudit
