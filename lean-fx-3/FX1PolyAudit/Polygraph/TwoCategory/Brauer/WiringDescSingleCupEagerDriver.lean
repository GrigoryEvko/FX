import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescSingleCupEagerDriver

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescSingleCupEagerDriver — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER r40 EAGER (prefix, region) single-cup driver: the two structural
`Nat` boolean-comparison self-lemmas (`bleSelf` / `bltSucc`), the EXACT-SLOT arrival certificate (`allSettledLeftOfCup`
/ `firstCupPosition` / `regionArrivedExact`) with its bridges (`regionArrivedExact_of_atomsRightZero` /
`regionArrivedExact_straddle`) and the recon §4 discrimination pins (`regionArrivedExact_discriminates` /
`regionArrivedExact_rejectsFalsePositive`), the factored untwist-run twin (`peelUntwistRunFactored`) + the eager
two-nested-structural driver (`eagerPeelUntwistThenDistant` / `eagerHostileUntwistThenDistant_demo` /
`eagerHostile_arrives`), the total dispatch DECISION (`eagerDispatchStep` / `eagerDispatch` / `eagerDispatch_probes` /
`straddleThenCap_notArrivedNaively`), the honesty marker, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the `Nat.blt`/`Nat.ble`
structural self-lemmas, the `RegionCupOutcome.prepend` NESTED-structural `peelUntwistRunFactored` recursion, the
`decide`-closed pure-list Bool pins, and the `firstCupPosition` + `allSettledLeftOfCup` folds are all axiom-free
(`List.length_append`, `Nat.beq_refl`, `Nat.succ_ne_zero`, `Nat.sub_*` LEAK `propext` and are deliberately avoided in
the imported source).  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.bleSelf
#assert_no_axioms FX1Poly.Polygraph.bltSucc
#assert_no_axioms FX1Poly.Polygraph.allSettledLeftOfCup
#assert_no_axioms FX1Poly.Polygraph.firstCupPosition
#assert_no_axioms FX1Poly.Polygraph.regionArrivedExact
#assert_no_axioms FX1Poly.Polygraph.regionArrivedExact_of_atomsRightZero
#assert_no_axioms FX1Poly.Polygraph.regionArrivedExact_straddle
#assert_no_axioms FX1Poly.Polygraph.regionArrivedExact_discriminates
#assert_no_axioms FX1Poly.Polygraph.regionArrivedExact_rejectsFalsePositive
#assert_no_axioms FX1Poly.Polygraph.peelUntwistRunFactored
#assert_no_axioms FX1Poly.Polygraph.eagerPeelUntwistThenDistant
#assert_no_axioms FX1Poly.Polygraph.eagerHostileUntwistThenDistant_demo
#assert_no_axioms FX1Poly.Polygraph.eagerHostile_arrives
#assert_no_axioms FX1Poly.Polygraph.eagerDispatchStep
#assert_no_axioms FX1Poly.Polygraph.eagerDispatch
#assert_no_axioms FX1Poly.Polygraph.eagerDispatch_probes
#assert_no_axioms FX1Poly.Polygraph.straddleThenCap_notArrivedNaively
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasEagerRegionDispatch
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_singleCupEagerDriverTerminalState

-- Independent cross-check (mandatory, per the AuditAll zero-axiom protocol): the headline declarations print no axioms.
#print axioms FX1Poly.Polygraph.regionArrivedExact_of_atomsRightZero
#print axioms FX1Poly.Polygraph.regionArrivedExact_straddle
#print axioms FX1Poly.Polygraph.eagerPeelUntwistThenDistant
#print axioms FX1Poly.Polygraph.eagerDispatch_probes
#print axioms FX1Poly.Polygraph.fxBrauer_singleCupEagerDriverTerminalState

end FX1PolyAudit
