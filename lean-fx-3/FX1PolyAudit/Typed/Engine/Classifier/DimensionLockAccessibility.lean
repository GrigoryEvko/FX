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

end FX1PolyAudit
