import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordCanonicity

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordCanonicityAudit — zero-axiom gate for the
recursive-comb STAIRCASE CANONICITY (WP-PROP r18, goal-chain item 2 of `CoxeterWordUnique`): the two engine
primitives (`natIndexOfValue`, `memBool`) + the strand-pin infrastructure + the injectivity kit + the canonicity
keystone, with the r9 / r11 / braid / width-5 non-vacuity fires and the separated unequal-perm pair.

Per-declaration `#assert_no_axioms` on every public def / theorem / marker, PLUS independent (non-fuel)
`#print axioms` on the engine primitives, the strand pin, the canonicity keystone, a non-vacuity fire, the separation
witness, and the marker.  The project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` closes
the gate. -/

namespace FX1PolyAudit

-- P0 — the two engine primitives + membership invariance.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMemBool
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatIndexOfValue
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMemBoolApplyAdjacentSwap

-- P2 — the strand pin (private helpers covered transitively).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSwapMovesValueDown
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRunBubblesFromIndex
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermExtendFixedTop
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermTopIndexOfPrefixRun

-- P4 — the DATA comb fold's final-state invariants.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombFoldInvariants

-- P5 — THE CANONICITY keystone.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombCanonicity

-- P6 — non-vacuity fires + the separation witness + the marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombCanonicity_r9
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombCanonicity_r11
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombCanonicity_braidPair
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombCanonicity_width5
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombCanonicity_unequalSeparated
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_hasRecursiveCombStaircaseCanonicity

-- Independent (non-fuel) axiom prints on the engine primitives, the strand pin, the canonicity keystone, a
-- non-vacuity fire, the separation witness, and the marker.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMemBool
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatIndexOfValue
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMemBoolApplyAdjacentSwap
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermTopIndexOfPrefixRun
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombCanonicity
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombCanonicity_r9
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombCanonicity_unequalSeparated
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_hasRecursiveCombStaircaseCanonicity

end FX1PolyAudit
