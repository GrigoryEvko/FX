import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Classifier.DimensionLockAccessibility

/-! # FX1PolyAudit/.../DimensionLockAccessibility — zero-axiom gate

Per-declaration zero-axiom gate for the Fitch affine-lock variable-accessibility predicate
(`isFibrantlyAccessibleAt`) and its unfolders / SR-mechanism lemma.  A `Bool`-valued structural recursion +
`rfl`-closed lemmas; must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.TypingContext.isFibrantlyAccessibleAt
#assert_no_axioms FX1Poly.Typed.isFibrantlyAccessibleAt_cons_zero
#assert_no_axioms FX1Poly.Typed.isFibrantlyAccessibleAt_lockCons_zero
#assert_no_axioms FX1Poly.Typed.isFibrantlyAccessibleAt_cons_succ
#assert_no_axioms FX1Poly.Typed.isFibrantlyAccessibleAt_lockCons_succ
#assert_no_axioms FX1Poly.Typed.dimensionIsNotFibrantlyAccessible
#assert_no_axioms FX1Poly.Typed.TypingContext.isLockFreeContext
#assert_no_axioms FX1Poly.Typed.isLockFreeContext_empty
#assert_no_axioms FX1Poly.Typed.isLockFreeContext_cons
#assert_no_axioms FX1Poly.Typed.isLockFreeContext_lockCons
#assert_no_axioms FX1Poly.Typed.TypingContext.lockFreeImpliesFibrantlyAccessible
#assert_no_axioms FX1Poly.Typed.fibrantlyAccessibleConsSucc
#assert_no_axioms FX1Poly.Typed.fibrantlyAccessibleLockConsSucc
#assert_no_axioms FX1Poly.Typed.TypingContext.isDimensionallyAccessibleAt
#assert_no_axioms FX1Poly.Typed.TypingContext.isAccessibleAtModality
#assert_no_axioms FX1Poly.Typed.isAccessibleAtModality_fibrant
#assert_no_axioms FX1Poly.Typed.isAccessibleAtModality_dimensional
#assert_no_axioms FX1Poly.Typed.TypingContext.isFibrantlyAccessibleAt_eq_not_isDimensionallyAccessibleAt
#assert_no_axioms FX1Poly.Typed.TypingContext.notUsableAtBothModalities
#assert_no_axioms FX1Poly.Typed.TypingContext.usableAtSomeModality
#assert_no_axioms FX1Poly.Typed.dimensionIsAccessibleDimensionally
#assert_no_axioms FX1Poly.Typed.consVarNotAccessibleDimensionally
#assert_no_axioms FX1Poly.Typed.dimensionIsNotAccessibleFibrantly
#assert_no_axioms FX1Poly.Typed.TypingContext.isSubjectUsableAtModality
#assert_no_axioms FX1Poly.Typed.isSubjectUsableAtModality_var
#assert_no_axioms FX1Poly.Typed.isSubjectUsableAtModality_dimensional_ofNonVarHead
#assert_no_axioms FX1Poly.Typed.isSubjectUsableAtModality_ofNonVarHead
#assert_no_axioms FX1Poly.Typed.TypingContext.lockFreeImpliesSubjectFibrantlyUsable
#assert_no_axioms FX1Poly.Typed.isDimensionFormer
#assert_no_axioms FX1Poly.Typed.generatorUsableAtModality
#assert_no_axioms FX1Poly.Typed.generatorUsableAtModality_fibrant
#assert_no_axioms FX1Poly.Typed.generatorUsableAtModality_dimensional
#assert_no_axioms FX1Poly.Typed.interval0IsDimensionFormer
#assert_no_axioms FX1Poly.Typed.intervalJoinIsDimensionFormer
#assert_no_axioms FX1Poly.Typed.pairIsNotDimensionFormer
#assert_no_axioms FX1Poly.Typed.intervalCodeIsNotDimensionFormer

end FX1PolyAudit
