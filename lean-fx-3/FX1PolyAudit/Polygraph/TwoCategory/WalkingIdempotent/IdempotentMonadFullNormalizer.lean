import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadFullNormalizer

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadFullNormalizer — zero-axiom gate

Per-declaration zero-axiom gate for the walking-idempotent-monad boundary-determined representative: the normal-form
representative `repNF`, its cell-independence, the transported total `repFull`, and its boundary-determinedness.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, and any well-founded
recursion (all matches STRUCTURAL). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.repNF
#assert_no_axioms FX1Poly.Polygraph.repNF_targetSucc
#assert_no_axioms FX1Poly.Polygraph.repNF_zeroZero
#assert_no_axioms FX1Poly.Polygraph.repNF_cellIndependent
#assert_no_axioms FX1Poly.Polygraph.repFull
#assert_no_axioms FX1Poly.Polygraph.repFull_boundary
#assert_no_axioms FX1Poly.Polygraph.fxIdempotentMonad_hasBoundaryRepresentative

end FX1PolyAudit
