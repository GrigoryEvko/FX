import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Fib.ContextComprehension

/-! # FX1PolyAudit.Typed.Fib.ContextComprehension — zero-axiom gate (fib-1c)

Per-declaration zero-axiom gate for the Core→Tier0/Context rewire: the forgetful comprehension object, the
cons / lockCons comprehension-extension identities, the representability-is-SubstVec-comprehension-iso tooth,
and the fib-1c headline (TypingContext.cons realizes the context axis's comprehension Γ.A). Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.TypingContext.comprehensionObject
#assert_no_axioms FX1Poly.Core.Fib.typingContextCons_comprehensionObject
#assert_no_axioms FX1Poly.Core.Fib.typingContextLockCons_comprehensionObject
#assert_no_axioms FX1Poly.Core.Fib.fxComprehensionCategory_representability_isSubstVecComprehensionIso
#assert_no_axioms FX1Poly.Core.Fib.typingContextCons_realizesComprehension

end FX1PolyAudit
