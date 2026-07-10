import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.DecisionTransfer

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.DecisionTransfer — zero-axiom gate for the decision transfer, the
concrete demonstrator (both verdicts), and the OMEGA-5 cell-side handoff (WP-AMALG-2 r1, B3)

Per-declaration zero-axiom gate: the modularity-routed decider, the four demonstrator verdicts (dispatch-map images
and the s-whiskered pair, isFalse and isTrue), the OMEGA-5 tensor `⊗_k` composition law and its two concrete legs,
and the three honesty markers (including the HELD `fxAmalg_hasDispatchTheorem` note).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the decision transfer through the B2 biconditional
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionMonadPushoutDecisionViaModularity

-- the concrete demonstrator, both verdicts (dispatch-map images + s-whiskered pair)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchedFaceSeparatingVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchedFaceReflexiveVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.modularityDecisionSeparatingVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.modularityDecisionReflexiveVerdict

-- the OMEGA-5 cell-side handoff: the tensor composition law + its two concrete legs
#assert_no_axioms FX1Poly.Polygraph.Amalgam.omegaFiveTensorComposition
#assert_no_axioms FX1Poly.Polygraph.Amalgam.omegaFiveTensorSoundnessLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.omegaFiveTensorSoundnessRight

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasDecisionTransfer
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasOmegaFiveCellSideHandoff
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_dispatchTheoremStaysWalled

end FX1PolyAudit
