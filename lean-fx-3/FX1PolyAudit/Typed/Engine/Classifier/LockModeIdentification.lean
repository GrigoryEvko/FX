import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Classifier.LockModeIdentification

/-! # FX1PolyAudit/.../LockModeIdentification — zero-axiom gate

Per-declaration zero-axiom gate for the lock/mode identification (LOCK-MODE-0 brick 1): the kernel's bespoke
`ObligationModality` IS the mode axis's `FibrancyKind`, and `isAccessibleAtModality` IS the mode match.

The load-bearing row is `isAccessibleAtModality_isModeMatch` — everything the re-founding does downstream
rides on it, so it is gated here before anything is moved.  Structural recursion over the telescope with the
propext-free `Fin` destructuring + full-enumeration matches on both two-element sorts; must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.obligationModalityToFibrancyKind
#assert_no_axioms FX1Poly.Typed.fibrancyKindToObligationModality
#assert_no_axioms FX1Poly.Typed.fibrancyKindToObligationModality_toFibrancyKind
#assert_no_axioms FX1Poly.Typed.obligationModalityToFibrancyKind_toObligationModality
#assert_no_axioms FX1Poly.Typed.TypingContext.bindingFibrancyMode
#assert_no_axioms FX1Poly.Typed.TypingContext.isFibrantlyAccessibleAt_isModeMatch
#assert_no_axioms FX1Poly.Typed.TypingContext.isDimensionallyAccessibleAt_isModeMatch
#assert_no_axioms FX1Poly.Typed.TypingContext.isAccessibleAtModality_isModeMatch
#assert_no_axioms FX1Poly.Typed.TypingContext.isAccessibleAtModality_ofFibrancyKind
#assert_no_axioms FX1Poly.Typed.TypingContext.lockedDimensionIsAtExotypeMode
#assert_no_axioms FX1Poly.Typed.TypingContext.consBindingIsAtFibrantMode
#assert_no_axioms FX1Poly.Typed.lockSeparatesTwoDistinctModes

end FX1PolyAudit
