import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Core.StepWordRewriteSoundness

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Core.StepWordRewriteSoundness

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Core.StepWordRewriteSoundness`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The forward half of the term-code-word bridge: FX reduction embeds into word rewriting over the
-- term-code monoid.  FxWordRewritesOneStep is one-step word rewriting (List Nat) under an FxTermRewriteRule
-- system (fire + left/right context closure).  Step.toWordRewrite is single-step soundness (the fire of the
-- system rule, with no typed-SN side condition since fxStepSystem holds every instantiated reduction as a
-- top-level rule).  FxWordRewritesMany is the refl-trans closure with single/trans + context lifts (a
-- congruence preorder); StepStar.toWordRewrites is many-step soundness by induction over the chain.
-- Zero-axiom: Prop inductives + constructor application + structural inductions.
#assert_no_axioms FX1Poly.Core.FxWordRewritesOneStep

#assert_no_axioms FX1Poly.Core.Step.toWordRewrite

#assert_no_axioms FX1Poly.Core.FxWordRewritesMany

#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.single

#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.trans

#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.underLeftContext

#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.underRightContext

#assert_no_axioms FX1Poly.Core.StepStar.toWordRewrites

end FX1PolyAudit
