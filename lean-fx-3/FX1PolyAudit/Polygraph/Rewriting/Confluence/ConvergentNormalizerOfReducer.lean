import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.Confluence.ConvergentNormalizerOfReducer

/-! # FX1PolyAudit.Polygraph.Rewriting.Confluence.ConvergentNormalizerOfReducer

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.Rewriting.Confluence.ConvergentNormalizerOfReducer`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.reducerNormalize

#assert_no_axioms FX1Poly.Core.reducerNormalize_unfold

#assert_no_axioms FX1Poly.Core.reducerNormalize_reducesTo

#assert_no_axioms FX1Poly.Core.reducerNormalize_isNormalForm

#assert_no_axioms FX1Poly.Core.ConvergentNormalizer.ofReducer

#assert_no_axioms FX1Poly.Core.decidableEquationalTheoryOfReducerSN

end FX1PolyAudit
