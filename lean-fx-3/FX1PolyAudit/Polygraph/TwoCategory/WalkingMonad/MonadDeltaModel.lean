import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadDeltaModel

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadDeltaModel — zero-axiom gate (the Δ model: covariant fold sound for the monad)

Per-declaration zero-axiom gate for the walking-monad Δ model: the retuned fold `monadMonoStepAtom` /
`monadMonotoneMapOf`, the generator smokes, the structural-fragment soundness leg, the three monad-law soundness
theorems (seed `rfl` + positive-width via the shipped simplicial / commutation identities), the canonicalization
structure, the decision assembly, and the honesty markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.MonadSaturatedCanonicalization
#assert_no_axioms FX1Poly.Polygraph.monadDecideSaturatedConvViaMonotoneMap
#assert_no_axioms FX1Poly.Polygraph.monadSaturatedWordProblemModuloCanonicalization
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasMonotoneMapFoldSoundOnLaws
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasMonotoneMapDecisionAssembled

end FX1PolyAudit
