import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStraightening

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescStraightening — zero-axiom gate (WP-BRAUER-4 r4)

Per-declaration zero-axiom gate for the two constructive straightening blocks landed in round 4: block (a) the
UNTWIST ABSORPTION with the `crossingCount` measure leg, and block (b) the FREE Coxeter moves (R2 cancel / R3 braid
/ distant commute) over the seven-relation over-approximation `BrauerConvFree7`, unconditional and in arbitrary
prefix / suffix context (the "suffix congruence is free" realization).  The private subtraction-free arithmetic
helpers are covered transitively.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- block (a): the crossing-count measure
#assert_no_axioms FX1Poly.Polygraph.crossingBit
#assert_no_axioms FX1Poly.Polygraph.crossingCount
#assert_no_axioms FX1Poly.Polygraph.crossingCount_append

-- block (a): the untwist rows at any position + absorption in arbitrary context + the strict measure drop
#assert_no_axioms FX1Poly.Polygraph.cupUntwistAt
#assert_no_axioms FX1Poly.Polygraph.capUntwistAt
#assert_no_axioms FX1Poly.Polygraph.cupUntwistAbsorb
#assert_no_axioms FX1Poly.Polygraph.capUntwistAbsorb
#assert_no_axioms FX1Poly.Polygraph.cupUntwist_crossingCount
#assert_no_axioms FX1Poly.Polygraph.capUntwist_crossingCount
#assert_no_axioms FX1Poly.Polygraph.cupUntwistAbsorb_crossingCount

-- block (b): the free Coxeter moves + their arbitrary-context (prefix / suffix) versions
#assert_no_axioms FX1Poly.Polygraph.crossingCancelFree
#assert_no_axioms FX1Poly.Polygraph.crossingBraidFree
#assert_no_axioms FX1Poly.Polygraph.crossingCommuteFree
#assert_no_axioms FX1Poly.Polygraph.crossingCancelFree_inContext
#assert_no_axioms FX1Poly.Polygraph.crossingBraidFree_inContext
#assert_no_axioms FX1Poly.Polygraph.crossingCommuteFree_inContext

-- non-vacuity: the r2 pair straightens (with its measure drop), an R3 pair, soundness intact
#assert_no_axioms FX1Poly.Polygraph.r2Pair_straightens
#assert_no_axioms FX1Poly.Polygraph.r3Pair_straightens
#assert_no_axioms FX1Poly.Polygraph.soundness_crossing_not_identity_preserved

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasUntwistAbsorption
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingWordFreeCoxeterMoves
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingStraighteningInsertionResidual

end FX1PolyAudit
