import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Conversion.ConvSubstPair

/-! # FX1PolyAudit/AuditConvSubstPair — two-variable substitution congruence audit shard

Per-declaration zero-axiom gate for the `substPair` raw-conversion congruence (the two-substituent analog
of `Conv.subst0`, consumed by the `idJ` output-type Conv-stability of the native eliminator-SR, #1740 gate 2
of #1697): the pointwise-StepStar bridge `RawTermSubst.pair_pointwise_stepStar` and the three-arg congruence
`Conv.substPair`.  Each must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTermSubst.pair_pointwise_stepStar
#assert_no_axioms FX1Poly.Core.Conv.substPair

end FX1PolyAudit
