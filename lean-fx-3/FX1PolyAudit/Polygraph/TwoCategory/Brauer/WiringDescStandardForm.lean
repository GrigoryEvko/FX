import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardForm

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescStandardForm — zero-axiom gate (WP-BRAUER COMPLETENESS r1)

Per-declaration zero-axiom gate for the completeness-rung round 1: the connectivity-congruence DECISION
(`brauerConv_complete` / `brauerConv_iff_diagram` / `decidableBrauerConv`), the permutation standard-form layer
(definitions + closed structural lemmas + readback smokes), and the three crossing-word Coxeter moves
(`brauerConv_crossing_{cancel,braid,commute}`) with their non-vacuity witnesses.  The private arithmetic /
append-nil helpers are covered transitively.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the connectivity-congruence decision
#assert_no_axioms FX1Poly.Polygraph.brauerConv_complete
#assert_no_axioms FX1Poly.Polygraph.brauerConv_iff_diagram
#assert_no_axioms FX1Poly.Polygraph.decidableBrauerConv
#assert_no_axioms FX1Poly.Polygraph.decideBrauerConvBool
#assert_no_axioms FX1Poly.Polygraph.decideBrauerConvBool_double_crossing
#assert_no_axioms FX1Poly.Polygraph.decideBrauerConvBool_crossing_ne_identity

-- the permutation standard-form definitions + closed structural lemmas
#assert_no_axioms FX1Poly.Polygraph.applyAdjacentSwap
#assert_no_axioms FX1Poly.Polygraph.crossingWord
#assert_no_axioms FX1Poly.Polygraph.permuteOfCrossingWord
#assert_no_axioms FX1Poly.Polygraph.natIndexOfValue
#assert_no_axioms FX1Poly.Polygraph.permutationDiagram
#assert_no_axioms FX1Poly.Polygraph.applyAdjacentSwap_length
#assert_no_axioms FX1Poly.Polygraph.crossingWord_length
#assert_no_axioms FX1Poly.Polygraph.foldlAdjacentSwap_length
#assert_no_axioms FX1Poly.Polygraph.permuteOfCrossingWord_length
#assert_no_axioms FX1Poly.Polygraph.permutationDiagram_shape

-- the readback smokes (validate the permutation / diagram alignment concretely)
#assert_no_axioms FX1Poly.Polygraph.readback_smoke_identity_two
#assert_no_axioms FX1Poly.Polygraph.readback_smoke_single_crossing
#assert_no_axioms FX1Poly.Polygraph.readback_smoke_double_crossing
#assert_no_axioms FX1Poly.Polygraph.readback_smoke_three_strand
#assert_no_axioms FX1Poly.Polygraph.readback_smoke_yangBaxter

-- the three crossing-word Coxeter moves (real relation firings) + non-vacuity
#assert_no_axioms FX1Poly.Polygraph.brauerConv_crossing_cancel
#assert_no_axioms FX1Poly.Polygraph.brauerConv_crossing_braid
#assert_no_axioms FX1Poly.Polygraph.brauerConv_crossing_commute
#assert_no_axioms FX1Poly.Polygraph.brauerConv_crossing_cancel_smoke
#assert_no_axioms FX1Poly.Polygraph.brauerConv_crossing_braid_smoke
#assert_no_axioms FX1Poly.Polygraph.brauerConv_crossing_commute_smoke

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasConnectivityCongruenceDecision
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasPermutationStandardForm
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingWordCoxeterMoves
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingOnlyStraightening
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFreeBrauerStraighteningNF

end FX1PolyAudit
