import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SaturationFuelBound

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SaturationFuelBound — zero-axiom gate

Per-declaration zero-axiom gate for the conditional BFS fuel discharge: the hand-rolled
length kit (append, map, the three filter-length lemmas, left-multiplication
monotonicity), the successor cap, the fresh-candidate counter with its three counting
lemmas, the one-step potential inequality, the conditional exhaustion theorem, the
certified fuel, and the class-enumeration-conditional decider.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.listLengthAppend
#assert_no_axioms FX1Poly.Polygraph.listLengthMap
#assert_no_axioms FX1Poly.Polygraph.listLengthFilterLe
#assert_no_axioms FX1Poly.Polygraph.listLengthFilterMono
#assert_no_axioms FX1Poly.Polygraph.listLengthFilterStrictMono
#assert_no_axioms FX1Poly.Polygraph.natMulLeftMono
#assert_no_axioms FX1Poly.Polygraph.swapSuccessors_lengthBound
#assert_no_axioms FX1Poly.Polygraph.isFreshAgainst
#assert_no_axioms FX1Poly.Polygraph.freshCandidateCount
#assert_no_axioms FX1Poly.Polygraph.isFreshAgainst_ofNotMem
#assert_no_axioms FX1Poly.Polygraph.isFreshAgainst_ofMem
#assert_no_axioms FX1Poly.Polygraph.notMem_ofIsFreshAgainst
#assert_no_axioms FX1Poly.Polygraph.freshCandidateCount_appendLe
#assert_no_axioms FX1Poly.Polygraph.freshCandidateCount_strictDecrease
#assert_no_axioms FX1Poly.Polygraph.freshCandidateCount_leClassLength
#assert_no_axioms FX1Poly.Polygraph.saturationPotentialStep
#assert_no_axioms FX1Poly.Polygraph.didExhaustFrontier_ofPotentialBound
#assert_no_axioms FX1Poly.Polygraph.classSaturationFuel
#assert_no_axioms FX1Poly.Polygraph.didExhaustFrontier_ofCompleteClassList
#assert_no_axioms FX1Poly.Polygraph.decideAtomicTraceEquivOfCompleteClassList

end FX1PolyAudit
