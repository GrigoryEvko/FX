import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.RuleTables.TypingRowDispatch

/-! # AuditTypingRowDispatch — zero-axiom gate for TYTAB-1 brick 2

The unified `TypingRow` lookup over the typing-table bundle: the `typingRowsOf` collector, its two
`List.Mem` helpers, all nineteen faithfulness theorems, and the canonical-generator computations.
Each pin must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.typingRowsOf
#assert_no_axioms FX1Poly.Typed.consMapped_mem_head
#assert_no_axioms FX1Poly.Typed.consMapped_mem_tail

#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_formation
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_flatFormation
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_baseType
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_termIndexedFormer
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_gradedIntro
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_generalElim
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_recursiveElim
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_twoBranchMatch
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_pathInduction
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_projection
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_listElim
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_dataIntroNullary
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_recursiveUnaryIntro
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_recursiveBinaryIntro
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_pinnedUnaryIntro
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_nullaryFreeTypeIntro
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_coproductIntro
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_nonDependentBinaryIntro
#assert_no_axioms FX1Poly.Typed.typingRowsOf_mem_reflexiveIntro

#assert_no_axioms FX1Poly.Typed.typingRowsOf_lam_singleton
#assert_no_axioms FX1Poly.Typed.typingRowsOf_app_singleton
#assert_no_axioms FX1Poly.Typed.typingRowsOf_piTyCode_singleton
#assert_no_axioms FX1Poly.Typed.typingRowsOf_var_empty

end FX1PolyAudit
