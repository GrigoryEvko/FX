import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeCasesReps

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeCasesReps — zero-axiom gate (cases helpers leaf)

Per-declaration zero-axiom gate for the bespoke-free CASES helpers leaf: the all-ones multiplicity data, the
run-peeling of the strictly-ascending identity map, and the monad-specific boundary-cast algebra — the nine
conv-FREE helpers relocated VERBATIM from `MonadNormalizeCases` so the survivor lane (and the idempotent-saturated
bricks) reach them conv-decoupled.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.monadOnes
#assert_no_axioms FX1Poly.Polygraph.length_monadOnes
#assert_no_axioms FX1Poly.Polygraph.countsDomainPath_monadOnes
#assert_no_axioms FX1Poly.Polygraph.runLengthAt_ascendingFrom_succ
#assert_no_axioms FX1Poly.Polygraph.dropRunAt_ascendingFrom_succ
#assert_no_axioms FX1Poly.Polygraph.countsOf_ascendingFrom_ones
#assert_no_axioms FX1Poly.Polygraph.monadWhiskerLeft_castBoundary
#assert_no_axioms FX1Poly.Polygraph.monadCastBoundary_castBoundary
#assert_no_axioms FX1Poly.Polygraph.monadCastBoundary_id

end FX1PolyAudit
