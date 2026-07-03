import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWireDistinct

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingWireDistinct — zero-axiom gate

Per-declaration zero-axiom gate for the open-wire distinctness invariant: the positional
predicate, the out-of-range normalizations, the per-step and fold preservation, and the seed
instances (the private zone/kit lemmas are covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.WireListDistinct
#assert_no_axioms FX1Poly.Polygraph.natListInsertAt_pastEnd
#assert_no_axioms FX1Poly.Polygraph.natListRemoveTwoAt_pastEnd
#assert_no_axioms FX1Poly.Polygraph.wireListDistinct_natListRemoveTwoAt
#assert_no_axioms FX1Poly.Polygraph.stepCup_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.stepCap_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.stepAtom_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.processSpine_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.canonicalMatchingSeed_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.processSpine_fromSeed_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingWireDistinctness

end FX1PolyAudit
