import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingSwapMapEquivariance

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingSwapMapEquivariance — zero-axiom gate

Per-declaration zero-axiom gate for the r14 (I1) swap renaming-equivariance leg: `natListSwapTwoAt_map` — the
faithful crossing's open-wire adjacent transposition commutes with any id renaming `sigma : Nat → Nat` in window
(`position + 1 < wires.length`), composed from the shipped `natListInsertAt_map` / `natListRemoveTwoAt_map` /
`natListGetAt_map_inRange`.  Plus its reachable-instance non-vacuity witness and the honesty marker + pins.

The lemma flips ONLY its own marker `fxMode_hasArcCrossingSwapMapEquivariance := true`; the permanent keystone pins
`fxMode_hasArcPeelGeneralSignature` and `fxMode_hasArcGodementSamePartitionFreshProof` stay `false` (re-asserted by
`rfl`).

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the two
are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- the swap equivariance lemma + its non-vacuity witness
#assert_no_axioms FX1Poly.Polygraph.natListSwapTwoAt_map
#assert_no_axioms FX1Poly.Polygraph.natListSwapTwoAt_map_seed_confirms

-- honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCrossingSwapMapEquivariance
#assert_no_axioms FX1Poly.Polygraph.arcCrossingSwapMapEquivariance_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCrossingSwapMapEquivariance_samePartitionFreshProof_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.natListSwapTwoAt_map
#print axioms FX1Poly.Polygraph.natListSwapTwoAt_map_seed_confirms
#print axioms FX1Poly.Polygraph.fxMode_hasArcCrossingSwapMapEquivariance
#print axioms FX1Poly.Polygraph.arcCrossingSwapMapEquivariance_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcCrossingSwapMapEquivariance_samePartitionFreshProof_stays_false

end FX1PolyAudit
