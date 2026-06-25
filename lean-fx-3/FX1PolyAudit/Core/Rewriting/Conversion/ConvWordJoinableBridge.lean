import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Conversion.ConvWordJoinableBridge

/-! # FX1PolyAudit.Core.Rewriting.Conversion.ConvWordJoinableBridge

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Conversion.ConvWordJoinableBridge`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The Conv-to-word-joinability bridge (forward half).  Conv is term joinability (StepStar.Join = common
-- reduct); FxWordJoinable is the ConvertibleModulo for the FX term-code word monoid (common word reduct).
-- Conv.toWordJoinable maps both StepStar legs via StepStar.toWordRewrites with common = commonTerm.toCode.
-- refl/symm establish a reflexive-symmetric relation; this gate does not include trans (which needs word
-- confluence) or the reverse direction (the word-to-term completeness gap).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.FxWordJoinable

#assert_no_axioms FX1Poly.Core.FxWordJoinable.refl

#assert_no_axioms FX1Poly.Core.FxWordJoinable.symm

#assert_no_axioms FX1Poly.Core.FxWordJoinable.ofWordRewritesMany

#assert_no_axioms FX1Poly.Core.Conv.toWordJoinable

#assert_no_axioms FX1Poly.Core.Step.toWordJoinable

end FX1PolyAudit
