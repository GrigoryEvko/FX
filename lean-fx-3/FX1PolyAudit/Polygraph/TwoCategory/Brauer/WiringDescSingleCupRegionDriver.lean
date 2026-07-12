import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescSingleCupRegionDriver

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescSingleCupRegionDriver — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER r39 REGION-TRACKED single-cup decision: the cap detector (`isCapAtom`),
the two structural bridge lemmas (`atomsRightOfFirstCup_eq_countAtoms_suffix` / `countAtoms_eq_zero_imp_nil`) and the
honest raw-arrival ⟹ factored-arrival bridge (`capFreeRight_of_arrived`), the FACTORED three-fated outcome
(`RegionCupOutcome`) + its prepend combinator, the factored terminal builders (`outcomeArrivedFactoredStraddle` /
`outcomeArrivedFactoredOfDistantTail` / `outcomeAnnihilatedFactoredS1` / `_S2`), the loop router
(`snakeLoopFree8_clean` / `outcomeLoopAtFactored`), the scan-and-classify total function (`classifyCupNeighbourStep` /
`classifyCupHeadTail` / `classifyFirstCupNeighbour` / `classifyNeighbour_probes`), the four hostiles + trace d run
through the factored outcome (`regionHostile*` / `RegionCupOutcome.fate` / `regionHostile_fates`), the blocker-1 pin
(`factoredArrival_where_rawFalseNegatives`), the honesty markers, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the indexed `RegionCupOutcome`
match in `prepend`/`fate` and the `Nat.add_comm` + `Nat.noConfusion` contradiction in `countAtoms_eq_zero_imp_nil` are
all axiom-free (`List.length_append`, `Nat.beq_refl`, `Nat.succ_ne_zero`, `Nat.sub_*` LEAK `propext` and are deliberately
avoided in the imported source).  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isCapAtom
#assert_no_axioms FX1Poly.Polygraph.isCapAtom_capAt
#assert_no_axioms FX1Poly.Polygraph.isCapAtom_cupAt
#assert_no_axioms FX1Poly.Polygraph.isCapAtom_crossingAt
#assert_no_axioms FX1Poly.Polygraph.atomsRightOfFirstCup_eq_countAtoms_suffix
#assert_no_axioms FX1Poly.Polygraph.countAtoms_eq_zero_imp_nil
#assert_no_axioms FX1Poly.Polygraph.capFreeRight_of_arrived
#assert_no_axioms FX1Poly.Polygraph.RegionCupOutcome.prepend
#assert_no_axioms FX1Poly.Polygraph.outcomeArrivedFactoredStraddle
#assert_no_axioms FX1Poly.Polygraph.outcomeArrivedFactoredOfDistantTail
#assert_no_axioms FX1Poly.Polygraph.outcomeAnnihilatedFactoredS1
#assert_no_axioms FX1Poly.Polygraph.outcomeAnnihilatedFactoredS2
#assert_no_axioms FX1Poly.Polygraph.snakeLoopFree8_clean
#assert_no_axioms FX1Poly.Polygraph.outcomeLoopAtFactored
#assert_no_axioms FX1Poly.Polygraph.classifyCupNeighbourStep
#assert_no_axioms FX1Poly.Polygraph.classifyCupHeadTail
#assert_no_axioms FX1Poly.Polygraph.classifyFirstCupNeighbour
#assert_no_axioms FX1Poly.Polygraph.classifyNeighbour_probes
#assert_no_axioms FX1Poly.Polygraph.RegionCupOutcome.fate
#assert_no_axioms FX1Poly.Polygraph.regionHostileStraddleArrived
#assert_no_axioms FX1Poly.Polygraph.regionHostileSnakeFirst
#assert_no_axioms FX1Poly.Polygraph.regionHostileUntwistDistant
#assert_no_axioms FX1Poly.Polygraph.regionHostileLoop
#assert_no_axioms FX1Poly.Polygraph.regionHostile_fates
#assert_no_axioms FX1Poly.Polygraph.factoredArrival_where_rawFalseNegatives
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFactoredCupArrival
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasRegionCupClassifier
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasRegionDriverTotalDispatch
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_singleCupRegionDriverTerminalState

-- Independent cross-check (mandatory, per the AuditAll zero-axiom protocol): the headline declarations print no axioms.
#print axioms FX1Poly.Polygraph.capFreeRight_of_arrived
#print axioms FX1Poly.Polygraph.RegionCupOutcome.prepend
#print axioms FX1Poly.Polygraph.outcomeArrivedFactoredStraddle
#print axioms FX1Poly.Polygraph.classifyFirstCupNeighbour
#print axioms FX1Poly.Polygraph.fxBrauer_singleCupRegionDriverTerminalState

end FX1PolyAudit
