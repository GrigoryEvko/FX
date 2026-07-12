import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingConsCongrStep

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingConsCongrStep — zero-axiom gate

Per-declaration zero-axiom gate for the r11 FAITHFUL CROSSING `consCongr` STEP: the two residuals a
general-signature faithful peel leaves open at a `2⇒2` crossing atom, plus their assembly into the
shipped-consCongr-arm-shaped five-invariant bundle.

The build: R1 (`arcStateFresh_stepCrossArc`, freshness preservation across the faithful crossing — every id in the
transposed open-wire list is an id of the original, via `mem_natListInsertAt_imp` / `mem_natListRemoveTwoAt_imp`
and the in-range reader `natListGetAt_mem_of_lt`, the other three freshness conjuncts on the nose); R2
(`stepCrossArc_openWires_tracksBoundary`, the boundary tracking law — `domBoundaryLength = codBoundaryLength` for a
`2⇒2` atom, width preserved by the r10 `stepCrossArc_openWires_length`, the in-window fit DERIVED from the entry
tracking + arity); and `arcFaithfulConsCongrStep_cross` (the five exit invariants at once — R1, the `rfl`-clean
forest / `nextFresh` legs by defeq, R2).  Non-vacuity: `arcFaithfulConsCongrStep_cross_seed_confirms` fires the
assembly at the width-2 fresh seed on the concrete `crossAtom`.

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the two
are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`.  (The private in-range reader `natListGetAt_mem_of_lt` is not a
public name; its cleanliness is verified transitively through `arcStateFresh_stepCrossArc`.) -/

namespace FX1PolyAudit

-- the arity predicate + the two residual providers
#assert_no_axioms FX1Poly.Polygraph.AtomHasCrossArity
#assert_no_axioms FX1Poly.Polygraph.arcStateFresh_stepCrossArc
#assert_no_axioms FX1Poly.Polygraph.stepCrossArc_openWires_tracksBoundary

-- the assembled faithful consCongr step + its non-vacuity witness
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulConsCongrStep_cross
#assert_no_axioms FX1Poly.Polygraph.arcFaithfulConsCongrStep_cross_seed_confirms

-- honesty marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCrossingConsCongrStep
#assert_no_axioms FX1Poly.Polygraph.arcCrossingConsCongrStep_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCrossingConsCongrStep_samePartitionFreshProof_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCrossingConsCongrStep_disjointBlockCommute_stays_true

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.AtomHasCrossArity
#print axioms FX1Poly.Polygraph.arcStateFresh_stepCrossArc
#print axioms FX1Poly.Polygraph.stepCrossArc_openWires_tracksBoundary
#print axioms FX1Poly.Polygraph.arcFaithfulConsCongrStep_cross
#print axioms FX1Poly.Polygraph.arcFaithfulConsCongrStep_cross_seed_confirms
#print axioms FX1Poly.Polygraph.fxMode_hasArcCrossingConsCongrStep
#print axioms FX1Poly.Polygraph.arcCrossingConsCongrStep_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcCrossingConsCongrStep_samePartitionFreshProof_stays_false
#print axioms FX1Poly.Polygraph.arcCrossingConsCongrStep_disjointBlockCommute_stays_true

end FX1PolyAudit
