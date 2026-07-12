import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingSwapDispatcher

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingSwapDispatcher — zero-axiom gate

Per-declaration zero-axiom gate for the r13 NINE-PAIR faithful swap DISPATCHER: the single kind-indexed entry
point `arcFaithfulSwapExtractRestCommute` that routes ALL NINE arity pairs of the faithful step's three arms
(cup `0⇒2` / cap `2⇒0` / cross `2⇒2`) to equal `rest`-spine extracts — the four cup/cap combos through the
sigma-renaming `ArcSwapCorePackage`, the five crossing combos through the five `congrArg` `rest`-corollaries off
the r10 / r12 state equalities.

The build: the kind machinery (`ArcSwapKind`, `stepArcOfKind`, `redexHighPosition` / `reductHighPosition`,
`redexTwoStep` / `reductTwoStep`, the nine-arm `swapWindowFits` disjoint-window bound — full enumeration, no
wildcard), the pivot→gap `Nat` bridge (`lowShiftDisjoint`, private, verified transitively), the five
cross-involving `rest`-corollaries, the nine-arm dispatcher, the two reachable-seed non-vacuity witnesses, and the
honesty marker + pins.  The dispatcher flips ONLY its own marker `fxMode_hasArcFaithfulSwapDispatcher := true`;
the permanent keystone pins `fxMode_hasArcPeelGeneralSignature` and `fxMode_hasArcGodementSamePartitionFreshProof`
stay `false` (re-asserted by `rfl`), and the provider markers stay `true`.

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the two
are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- the kind machinery (the swapWindowFits Prop-match is the propext trap the full-enumeration avoids)
#assert_no_axioms FX1Poly.Polygraph.stepArcOfKind
#assert_no_axioms FX1Poly.Polygraph.redexHighPosition
#assert_no_axioms FX1Poly.Polygraph.reductHighPosition
#assert_no_axioms FX1Poly.Polygraph.redexTwoStep
#assert_no_axioms FX1Poly.Polygraph.reductTwoStep
#assert_no_axioms FX1Poly.Polygraph.swapWindowFits

-- the five cross-involving rest-corollaries (the missing ofSwap providers)
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_rest_of_cupCrossSwap
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_rest_of_crossCupSwap
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_rest_of_capCrossSwap
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_rest_of_crossCapSwap
#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_rest_of_crossCrossSwap

-- the nine-pair dispatcher
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulSwapExtractRestCommute

-- non-vacuity witnesses (the reachable initial seed, both routes)
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulSwapDispatcher_cupCupSeed_confirms
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulSwapDispatcher_crossCrossSeed_confirms

-- honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulSwapDispatcher
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulSwapDispatcher_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulSwapDispatcher_samePartitionFreshProof_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulSwapDispatcher_heteroBlockCommute_stays_true
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulSwapDispatcher_disjointBlockCommute_stays_true
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulSwapDispatcher_swapCorePackage_stays_true

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.stepArcOfKind
#print axioms FX1Poly.Polygraph.redexHighPosition
#print axioms FX1Poly.Polygraph.reductHighPosition
#print axioms FX1Poly.Polygraph.redexTwoStep
#print axioms FX1Poly.Polygraph.reductTwoStep
#print axioms FX1Poly.Polygraph.swapWindowFits
#print axioms FX1Poly.Polygraph.extractArc_eq_rest_of_cupCrossSwap
#print axioms FX1Poly.Polygraph.extractArc_eq_rest_of_crossCupSwap
#print axioms FX1Poly.Polygraph.extractArc_eq_rest_of_capCrossSwap
#print axioms FX1Poly.Polygraph.extractArc_eq_rest_of_crossCapSwap
#print axioms FX1Poly.Polygraph.extractArc_eq_rest_of_crossCrossSwap
#print axioms FX1Poly.Polygraph.arcFaithfulSwapExtractRestCommute
#print axioms FX1Poly.Polygraph.arcFaithfulSwapDispatcher_cupCupSeed_confirms
#print axioms FX1Poly.Polygraph.arcFaithfulSwapDispatcher_crossCrossSeed_confirms
#print axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulSwapDispatcher
#print axioms FX1Poly.Polygraph.arcFaithfulSwapDispatcher_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulSwapDispatcher_samePartitionFreshProof_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulSwapDispatcher_heteroBlockCommute_stays_true
#print axioms FX1Poly.Polygraph.arcFaithfulSwapDispatcher_disjointBlockCommute_stays_true
#print axioms FX1Poly.Polygraph.arcFaithfulSwapDispatcher_swapCorePackage_stays_true

end FX1PolyAudit
