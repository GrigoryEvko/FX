import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Validity.TypedAtUniverseFibrantlyUsable

/-! # FX1PolyAudit/.../TypedAtUniverseFibrantlyUsable — zero-axiom gate

Per-declaration zero-axiom gate for the typed-implies-fibrantly-usable bridge engine
(#1829 A1-CONJUNCT-WIRE rigorous core): the cell substrate (`rename_intervalTypeCell`,
`intervalTypeCell_not_conv_universeCodeCell`), the interval-lock discipline
(`AllLocksAreInterval` + accessors + `lockedLookupIsInterval`), and the parameterized bridge
(`typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval`).  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.rename_intervalTypeCell
#assert_no_axioms FX1Poly.Typed.intervalTypeCell_not_conv_universeCodeCell
#assert_no_axioms FX1Poly.Typed.TypingContext.AllLocksAreInterval
#assert_no_axioms FX1Poly.Typed.TypingContext.AllLocksAreInterval.empty
#assert_no_axioms FX1Poly.Typed.TypingContext.AllLocksAreInterval.cons
#assert_no_axioms FX1Poly.Typed.TypingContext.AllLocksAreInterval.lockConsInterval
#assert_no_axioms FX1Poly.Typed.TypingContext.AllLocksAreInterval.ofCons
#assert_no_axioms FX1Poly.Typed.TypingContext.AllLocksAreInterval.ofLockCons
#assert_no_axioms FX1Poly.Typed.TypingContext.lockedLookupIsInterval
#assert_no_axioms FX1Poly.Typed.typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval

end FX1PolyAudit
