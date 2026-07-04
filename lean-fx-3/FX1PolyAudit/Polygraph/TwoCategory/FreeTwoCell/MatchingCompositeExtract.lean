import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCompositeExtract

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingCompositeExtract — zero-axiom gate

Per-declaration zero-axiom gate for the run-level extract agreement of two disciplined
second-half spines over a shared mid-state.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.processSpine_extract_eq_ofCanonicalExtractEq
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCompositeExtractAgreement

end FX1PolyAudit
