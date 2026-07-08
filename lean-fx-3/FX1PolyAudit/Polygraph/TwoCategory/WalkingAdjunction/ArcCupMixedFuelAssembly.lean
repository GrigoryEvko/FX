import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupMixedFuelAssembly

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupMixedFuelAssembly — zero-axiom gate

Per-declaration zero-axiom gate for the round-3 mixed fuel assembly: `MixedTailArcCompleteness` landed
from the per-boundary chained head extraction (`mixedTailArcCompleteness_ofChainedExtraction`, the
structural peel-and-recurse) and from the general cup orbit witness
(`mixedTailArcCompleteness_ofOrbitWitness`, arity dispatch with the cap branch discharged head-first).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.mixedTailArcCompleteness_ofChainedExtraction
#assert_no_axioms FX1Poly.Polygraph.mixedTailArcCompleteness_ofOrbitWitness
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupMixedFuelAssembly

end FX1PolyAudit
