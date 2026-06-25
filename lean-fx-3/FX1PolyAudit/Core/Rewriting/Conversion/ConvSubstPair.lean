import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Conversion.ConvSubstPair

/-! # FX1PolyAudit.Core.Rewriting.Conversion.ConvSubstPair

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Conversion.ConvSubstPair`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTermSubst.pair_pointwise_stepStar

#assert_no_axioms FX1Poly.Core.Conv.substPair

end FX1PolyAudit
