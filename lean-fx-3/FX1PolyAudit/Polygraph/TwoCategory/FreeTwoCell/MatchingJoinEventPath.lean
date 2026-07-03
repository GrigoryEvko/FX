import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventPath

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingJoinEventPath — zero-axiom gate

Per-declaration zero-axiom gate for the alternating-path characterization of the event fold:
the step/path inductives, the equivalence kit, assembly, and the decomposition chain.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.JoinEventStep
#assert_no_axioms FX1Poly.Polygraph.JoinEventPath
#assert_no_axioms FX1Poly.Polygraph.joinEventPath_ofStep
#assert_no_axioms FX1Poly.Polygraph.joinEventStep_symm
#assert_no_axioms FX1Poly.Polygraph.joinEventPath_append
#assert_no_axioms FX1Poly.Polygraph.joinEventPath_symm
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_applyJoinEvents_ofPath
#assert_no_axioms FX1Poly.Polygraph.joinEventPath_ofJoinStep
#assert_no_axioms FX1Poly.Polygraph.joinEventPath_ofJoinedBasePath
#assert_no_axioms FX1Poly.Polygraph.joinEventPath_ofFold
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasJoinEventPathCharacterization

end FX1PolyAudit
