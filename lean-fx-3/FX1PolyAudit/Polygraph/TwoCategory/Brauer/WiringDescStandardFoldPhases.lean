import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldPhases

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldPhases — zero-axiom gate (BRAUER-MIDDLE r4,
R3-A machinery)

Per-declaration zero-axiom gate for the cup / cap phase-fold connectivity inductions: the propext-free list kit
(`flattenNatPairs` + its append / length / membership lemmas), the two new phase-atom lemmas
(`stepWiring_cup_head` / `stepWiring_cap_head`), the two phase folds (`capFold_consumes` / `cupFold_creates`),
their non-vacuity smokes, and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.flattenNatPairs
#assert_no_axioms FX1Poly.Polygraph.flattenNatPairs_appendSingleton
#assert_no_axioms FX1Poly.Polygraph.appendPairRegroup
#assert_no_axioms FX1Poly.Polygraph.lengthAppendSingleton
#assert_no_axioms FX1Poly.Polygraph.natPairMemAppendSingleton
#assert_no_axioms FX1Poly.Polygraph.stepWiring_cup_head
#assert_no_axioms FX1Poly.Polygraph.stepWiring_cap_head
#assert_no_axioms FX1Poly.Polygraph.capFold_consumes
#assert_no_axioms FX1Poly.Polygraph.cupFold_creates
#assert_no_axioms FX1Poly.Polygraph.capFold_consumes_twoCaps
#assert_no_axioms FX1Poly.Polygraph.cupFold_creates_twoCups
#assert_no_axioms FX1Poly.Polygraph.cupFold_twoCups_diagram
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCupCapPhaseFolds
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasExt5CorrectedRoundtripFromPhaseFolds

end FX1PolyAudit
