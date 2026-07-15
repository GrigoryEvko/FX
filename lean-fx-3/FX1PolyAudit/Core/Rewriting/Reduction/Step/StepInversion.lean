import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Reduction.Step.StepInversion

/-! # FX1PolyAudit.Core.Rewriting.Reduction.Step.StepInversion

Zero-axiom audit shard mirroring kernel module
`FX1Poly.Core.Rewriting.Reduction.Step.StepInversion` — the shared two-child spine slot
decomposition (`StepChildren.invertTwoChildSpine`) and every root inversion that consumes it,
either directly (the arity-2 value/type-code family) or through a two-level peel (the arity-4
dependent-eliminator family).  Casing an indexed `StepChildren` at a `childCons` index is a
recorded propext hazard, so the brick and all twenty of its consumers are gated here rather than
resting on the namespace sweep alone.  Each declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.StepChildren.no_step_at_empty_spine
#assert_no_axioms FX1Poly.Core.StepChildren.invertTwoChildSpine

#assert_no_axioms FX1Poly.Core.Step.from_lam
#assert_no_axioms FX1Poly.Core.Step.from_pair
#assert_no_axioms FX1Poly.Core.Step.from_listCons
#assert_no_axioms FX1Poly.Core.Step.from_glueIntro
#assert_no_axioms FX1Poly.Core.Step.from_arrowCode
#assert_no_axioms FX1Poly.Core.Step.from_productCode
#assert_no_axioms FX1Poly.Core.Step.from_sumCode
#assert_no_axioms FX1Poly.Core.Step.from_eitherCode
#assert_no_axioms FX1Poly.Core.Step.from_equivCode
#assert_no_axioms FX1Poly.Core.Step.from_piTyCode
#assert_no_axioms FX1Poly.Core.Step.from_sigmaTyCode
#assert_no_axioms FX1Poly.Core.Step.from_polyFunctor
#assert_no_axioms FX1Poly.Core.Step.from_app
#assert_no_axioms FX1Poly.Core.Step.from_pathApp

#assert_no_axioms FX1Poly.Core.Step.from_boolElim
#assert_no_axioms FX1Poly.Core.Step.from_natElim
#assert_no_axioms FX1Poly.Core.Step.from_natRec
#assert_no_axioms FX1Poly.Core.Step.from_listElim
#assert_no_axioms FX1Poly.Core.Step.from_optionMatch
#assert_no_axioms FX1Poly.Core.Step.from_eitherMatch

end FX1PolyAudit
