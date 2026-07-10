import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentLawRelation

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentLawRelation — zero-axiom gate (the four idempotent laws)

Per-declaration zero-axiom gate for the bespoke-free idempotent law relation `IdempotentLawRel` (the four
walking-idempotent-monad laws as a `CellRel`) and the non-vacuity row `idempotenceRowConv`.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.IdempotentLawRel
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotenceRowConv

end FX1PolyAudit
