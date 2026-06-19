import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Confluence.ConvergentNormalizerOfReducer

/-! # FX1PolyAudit/AuditConvergentNormalizerOfReducer — zero-axiom gate for the generic normalizer builder

Per-declaration zero-axiom gate for `FX1Poly/Core/Rewriting/Confluence/ConvergentNormalizerOfReducer.lean`:
the `Acc.rec` abstract normalizer (`reducerNormalize`), its `rfl` unfold, the reach + normal-form facts, the
`ConvergentNormalizer.ofReducer` bundle, and the end-to-end `decidableEquationalTheoryOfReducerSN`.

This is the GENERIC bridge from "strongly-normalizing confluent relation + sound+complete deterministic
reducer" to a real decision procedure — built by `Acc.rec` (axiom-free large elimination of the `Prop`-valued
`Acc`), NOT `WellFounded.fix`.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.reducerNormalize
#assert_no_axioms FX1Poly.Core.reducerNormalize_unfold
#assert_no_axioms FX1Poly.Core.reducerNormalize_reducesTo
#assert_no_axioms FX1Poly.Core.reducerNormalize_isNormalForm
#assert_no_axioms FX1Poly.Core.ConvergentNormalizer.ofReducer
#assert_no_axioms FX1Poly.Core.decidableEquationalTheoryOfReducerSN

end FX1PolyAudit
