import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcDescent

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcDescent — zero-axiom gate (BRAUER-ARC-DESCENT r1, B1)

Per-declaration zero-axiom gate for the distinguished-arc lexicographic descent measure: the cup detector and its
reduction lemmas, the arc-structure counts and their append laws, the two prefix-whiskerings, the per-move suffix
cores, the whiskered strict descents (cup-past-cap / cup-past-crossing / cup-past-cup), the `Nat`-embedded
`arcMeasure` with its two lex→`Nat` combine lemmas, the non-vacuity evals on the minimal interleaved instance, and
the straddle-resister wall theorem + the two honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the cup detector + reductions
#assert_no_axioms FX1Poly.Polygraph.isCupAtom
#assert_no_axioms FX1Poly.Polygraph.isCupAtom_cupAt
#assert_no_axioms FX1Poly.Polygraph.isCupAtom_capAt
#assert_no_axioms FX1Poly.Polygraph.isCupAtom_crossingAt

-- the arc-structure counts + append laws
#assert_no_axioms FX1Poly.Polygraph.nonCupCount
#assert_no_axioms FX1Poly.Polygraph.cupCount
#assert_no_axioms FX1Poly.Polygraph.cupNonCupInversions
#assert_no_axioms FX1Poly.Polygraph.cupPositionSum
#assert_no_axioms FX1Poly.Polygraph.nonCupCount_append
#assert_no_axioms FX1Poly.Polygraph.cupPositionSum_append

-- the prefix-whiskerings + per-move suffix cores
#assert_no_axioms FX1Poly.Polygraph.cupNonCupInversions_prefix
#assert_no_axioms FX1Poly.Polygraph.cupPositionSum_prefix
#assert_no_axioms FX1Poly.Polygraph.cupInv_core_cupCap
#assert_no_axioms FX1Poly.Polygraph.cupInv_core_cupCrossing
#assert_no_axioms FX1Poly.Polygraph.cupInv_core_cupCup
#assert_no_axioms FX1Poly.Polygraph.nonCupCount_core_cupCap
#assert_no_axioms FX1Poly.Polygraph.nonCupCount_core_cupCrossing
#assert_no_axioms FX1Poly.Polygraph.cupPos_core_cupCup
#assert_no_axioms FX1Poly.Polygraph.cupPos_core_cupCup_suffix

-- the whiskered strict descents
#assert_no_axioms FX1Poly.Polygraph.cupCap_inversions_descends
#assert_no_axioms FX1Poly.Polygraph.cupCap_inversions_lt
#assert_no_axioms FX1Poly.Polygraph.cupCrossing_inversions_descends
#assert_no_axioms FX1Poly.Polygraph.cupCrossing_inversions_lt
#assert_no_axioms FX1Poly.Polygraph.cupCup_inversions_eq
#assert_no_axioms FX1Poly.Polygraph.cupCup_positions_descends
#assert_no_axioms FX1Poly.Polygraph.cupCup_positions_lt

-- the Nat embedding + combine lemmas
#assert_no_axioms FX1Poly.Polygraph.arcMeasure
#assert_no_axioms FX1Poly.Polygraph.arcMeasure_lt_of_primary
#assert_no_axioms FX1Poly.Polygraph.arcMeasure_lt_of_secondary

-- the non-vacuity evals + the straddle resister + markers
#assert_no_axioms FX1Poly.Polygraph.arcDescent_nonVacuity_cupCap
#assert_no_axioms FX1Poly.Polygraph.arcDescent_nonVacuity_cupCup
#assert_no_axioms FX1Poly.Polygraph.straddle_resists_arcMeasure
#assert_no_axioms FX1Poly.Polygraph.straddle_isMove
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasArcDescentMeasure
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasArcDescentFullMonovariant

end FX1PolyAudit
