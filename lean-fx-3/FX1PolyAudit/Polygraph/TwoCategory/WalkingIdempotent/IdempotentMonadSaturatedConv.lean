import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadSaturatedConv

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadSaturatedConv — zero-axiom gate (the idempotence-law convertibility)

Per-declaration zero-axiom gate for the walking-idempotent-monad saturated convertibility: the relation, the
idempotence witness, the `ofMonad` lift, and the monad-law / whiskered / coherence smokes.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.IdempotentMonadSaturatedTwoCellConv
#assert_no_axioms FX1Poly.Polygraph.idempotenceLawHolds
#assert_no_axioms FX1Poly.Polygraph.IdempotentMonadSaturatedTwoCellConv.ofMonadLaw
#assert_no_axioms FX1Poly.Polygraph.idempotentLeftUnitHolds
#assert_no_axioms FX1Poly.Polygraph.idempotentAssocHolds
#assert_no_axioms FX1Poly.Polygraph.idempotenceWhiskeredHolds
#assert_no_axioms FX1Poly.Polygraph.idempotentFacesCohere
#assert_no_axioms FX1Poly.Polygraph.fxIdempotentMonad_hasSaturatedConvWithIdempotence

end FX1PolyAudit
