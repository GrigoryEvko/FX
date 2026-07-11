import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapHeadExtractionWordPinPrime

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringCapHeadExtractionWordPinPrime — zero-axiom gate
(FC-3 r25, B3)

Per-declaration zero-axiom gate for the AllCapArity-augmented cap-head pin-prime and its conditional sort.  Must
be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- B3 — the AllCapArity-augmented cap-head pin-prime Prop
#assert_no_axioms FX1Poly.Polygraph.StringCapHeadExtractionWordPinPrime

-- B3 — the pure-cap sort re-wired to consume the pin-prime + honesty marker
#assert_no_axioms FX1Poly.Polygraph.stringPureCapSpine_sort_ofPrime
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCapHeadExtractionWordPinPrime

end FX1PolyAudit
