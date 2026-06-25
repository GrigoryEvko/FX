import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleTypeRename

/-! # FX1PolyAudit.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleTypeRename

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleTypeRename`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The neutral leaf of the stratified ReducibleTypeStep rename-closure (type + member level): the structural
-- fragment, separate from the Kripke-indexed piType arm (see the StratifiedReducibleTypeRename docstring).
#assert_no_axioms FX1Poly.Core.ReducibleTypeStep.neutralRename_of_leftInverse

#assert_no_axioms FX1Poly.Core.ReducibleTypeStep.neutralRenameMember_of_leftInverse

end FX1PolyAudit
