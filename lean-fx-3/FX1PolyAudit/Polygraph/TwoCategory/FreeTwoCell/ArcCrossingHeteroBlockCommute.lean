import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingHeteroBlockCommute

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingHeteroBlockCommute — zero-axiom gate

Per-declaration zero-axiom gate for the r12 (R3) HETEROGENEOUS crossing × cup/cap disjoint commutes: the four
mixed arity-pair `ofSwap` arms a general-signature swap dispatcher needs — cup/cap LEFT × cross RIGHT (`+2` /
`-2` offset) and cross LEFT × cup/cap RIGHT (no shift), each yielding the SAME `ArcWireState` in both firing
orders, hence the same extract, UNCONDITIONALLY (no perfect-matching regime).

The build: two new swap shift laws (`natListSwapTwoAt_succ` / `natListSwapTwoAt_appendPrefix`, plus the
`_zero_cons_cons` / `_prependTwo` reductions and `natListRemoveTwoAt_prependTwo`), the four `openWires` offset
commutes (`natListInsertAt_swapAbove_commute` / `natListSwapTwoAt_insertAbove_commute` /
`natListRemoveTwoAt_swapAbove_commute` / `natListSwapTwoAt_removeAbove_commute`, structural induction in the
shipped `gap`-convention over `ArcWindowCommutation`'s `natListRemoveTwoAt_succ` / `natListInsertAt_zero` /
append-prefix kit), the cap wire-read agreement (`natListGetAt_natListSwapTwoAt_below` / `_above`, off the r8
`natListGetAt_natListSwapTwoAt` + `transposeAdjacent_other`), the four state commutes, the four extract
commutes (`congrArg`), and the fresh-seed non-vacuity witnesses.  Private plumbing (the propext-free
`heteroRangeLength`, `heteroSeed`, the two `Nat` inequality helpers) is verified transitively through the public
names.

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the two
are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- the two new swap shift laws + the reductions the offset algebra bottoms out in
#assert_no_axioms FX1Poly.Polygraph.natListSwapTwoAt_succ
#assert_no_axioms FX1Poly.Polygraph.natListSwapTwoAt_zero_cons_cons
#assert_no_axioms FX1Poly.Polygraph.natListSwapTwoAt_prependTwo
#assert_no_axioms FX1Poly.Polygraph.natListRemoveTwoAt_prependTwo
#assert_no_axioms FX1Poly.Polygraph.natListSwapTwoAt_appendPrefix

-- the four openWires offset commutation laws (the genuine new math)
#assert_no_axioms FX1Poly.Polygraph.natListInsertAt_swapAbove_commute
#assert_no_axioms FX1Poly.Polygraph.natListSwapTwoAt_insertAbove_commute
#assert_no_axioms FX1Poly.Polygraph.natListRemoveTwoAt_swapAbove_commute
#assert_no_axioms FX1Poly.Polygraph.natListSwapTwoAt_removeAbove_commute

-- the cap wire-read agreement (crossing outside the read window)
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_natListSwapTwoAt_below
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_natListSwapTwoAt_above

-- the four state-level heterogeneous commutes
#assert_no_axioms FX1Poly.Polygraph.stepCrossArc_stepCupArc_heteroCommute
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_stepCrossArc_heteroCommute
#assert_no_axioms FX1Poly.Polygraph.stepCrossArc_stepCapArc_heteroCommute
#assert_no_axioms FX1Poly.Polygraph.stepCapArc_stepCrossArc_heteroCommute

-- the four whole-extract commutes
#assert_no_axioms FX1Poly.Polygraph.extractArc_stepCrossArc_stepCupArc_disjointCommute
#assert_no_axioms FX1Poly.Polygraph.extractArc_stepCupArc_stepCrossArc_disjointCommute
#assert_no_axioms FX1Poly.Polygraph.extractArc_stepCrossArc_stepCapArc_disjointCommute
#assert_no_axioms FX1Poly.Polygraph.extractArc_stepCapArc_stepCrossArc_disjointCommute

-- non-vacuity witnesses (fresh seed)
#assert_no_axioms FX1Poly.Polygraph.arcCrossingHeteroBlockCommute_cupSeed_confirms
#assert_no_axioms FX1Poly.Polygraph.arcCrossingHeteroBlockCommute_capSeed_confirms

-- honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCrossingHeteroBlockCommute
#assert_no_axioms FX1Poly.Polygraph.arcCrossingHeteroBlockCommute_disjointBlockCommute_stays_true
#assert_no_axioms FX1Poly.Polygraph.arcCrossingHeteroBlockCommute_consCongrStep_stays_true
#assert_no_axioms FX1Poly.Polygraph.arcCrossingHeteroBlockCommute_windowOpCommutation_stays_true
#assert_no_axioms FX1Poly.Polygraph.arcCrossingHeteroBlockCommute_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCrossingHeteroBlockCommute_samePartitionFreshProof_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.natListSwapTwoAt_succ
#print axioms FX1Poly.Polygraph.natListSwapTwoAt_appendPrefix
#print axioms FX1Poly.Polygraph.natListInsertAt_swapAbove_commute
#print axioms FX1Poly.Polygraph.natListSwapTwoAt_insertAbove_commute
#print axioms FX1Poly.Polygraph.natListRemoveTwoAt_swapAbove_commute
#print axioms FX1Poly.Polygraph.natListSwapTwoAt_removeAbove_commute
#print axioms FX1Poly.Polygraph.natListGetAt_natListSwapTwoAt_below
#print axioms FX1Poly.Polygraph.natListGetAt_natListSwapTwoAt_above
#print axioms FX1Poly.Polygraph.stepCrossArc_stepCupArc_heteroCommute
#print axioms FX1Poly.Polygraph.stepCupArc_stepCrossArc_heteroCommute
#print axioms FX1Poly.Polygraph.stepCrossArc_stepCapArc_heteroCommute
#print axioms FX1Poly.Polygraph.stepCapArc_stepCrossArc_heteroCommute
#print axioms FX1Poly.Polygraph.extractArc_stepCrossArc_stepCupArc_disjointCommute
#print axioms FX1Poly.Polygraph.extractArc_stepCupArc_stepCrossArc_disjointCommute
#print axioms FX1Poly.Polygraph.extractArc_stepCrossArc_stepCapArc_disjointCommute
#print axioms FX1Poly.Polygraph.extractArc_stepCapArc_stepCrossArc_disjointCommute
#print axioms FX1Poly.Polygraph.arcCrossingHeteroBlockCommute_cupSeed_confirms
#print axioms FX1Poly.Polygraph.arcCrossingHeteroBlockCommute_capSeed_confirms
#print axioms FX1Poly.Polygraph.fxMode_hasArcCrossingHeteroBlockCommute
#print axioms FX1Poly.Polygraph.arcCrossingHeteroBlockCommute_disjointBlockCommute_stays_true
#print axioms FX1Poly.Polygraph.arcCrossingHeteroBlockCommute_consCongrStep_stays_true
#print axioms FX1Poly.Polygraph.arcCrossingHeteroBlockCommute_windowOpCommutation_stays_true
#print axioms FX1Poly.Polygraph.arcCrossingHeteroBlockCommute_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcCrossingHeteroBlockCommute_samePartitionFreshProof_stays_false

end FX1PolyAudit
