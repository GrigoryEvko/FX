import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleLevelCongr

/-! # FX1PolyAudit.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleLevelCongr

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleLevelCongr`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Candidate-congruence of the stratified reducibility step-functor under lower-existence-equivalence: the
-- inductive step of level-irrelevance (Pi case via ofPointwiseIff, universe case via the lower-existence
-- equivalence).  The level-0 degenerate base means it does not bootstrap full irrelevance alone (see the module
-- docstring); it is the hard core a level argument reuses.
#assert_no_axioms FX1Poly.Core.ReducibleTypeStep.existsCongr

end FX1PolyAudit
