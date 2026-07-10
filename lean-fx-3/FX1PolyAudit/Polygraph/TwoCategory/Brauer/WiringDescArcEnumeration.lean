import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcEnumeration

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcEnumeration — zero-axiom gate (BRAUER-MIDDLE r13 T-ENUM E1)

Per-declaration zero-axiom gate for the arc-enumeration soundness half (E1) of T-ENUM: the well-formedness gate
(`IsBoundaryInvolution`), the four `filterMap` enumeration-soundness lemmas, the `cupArcTops` `− bottomCount`
exactness, the partition skeleton, the involution-gated cap + cup "each arc once" dedup, the conjugator base cases,
the non-vacuity firings, the honesty markers, and the machine-checked r13 ledger.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the well-formedness gate
#assert_no_axioms FX1Poly.Polygraph.IsBoundaryInvolution

-- the four enumeration-soundness lemmas
#assert_no_axioms FX1Poly.Polygraph.capArcFeetIndices_mem_sound
#assert_no_axioms FX1Poly.Polygraph.throughStrandBottoms_mem_sound
#assert_no_axioms FX1Poly.Polygraph.throughStrandTops_mem_sound
#assert_no_axioms FX1Poly.Polygraph.cupArcTopIndices_mem_sound

-- the cupArcTops − bottomCount exactness + the partition skeleton
#assert_no_axioms FX1Poly.Polygraph.cupArcTop_sub_exact
#assert_no_axioms FX1Poly.Polygraph.capFoot_not_throughBottom

-- the involution-gated cap + cup dedup
#assert_no_axioms FX1Poly.Polygraph.capArcFeetIndices_arc_closes
#assert_no_axioms FX1Poly.Polygraph.capArcFeetIndices_excludes_larger_foot
#assert_no_axioms FX1Poly.Polygraph.cupArcTopIndices_excludes_larger_foot

-- the E2 conjugator base cases
#assert_no_axioms FX1Poly.Polygraph.descendingSwapPositions_self
#assert_no_axioms FX1Poly.Polygraph.descendingSwapPositions_ofLe
#assert_no_axioms FX1Poly.Polygraph.permutationToCrossingWord_zero
#assert_no_axioms FX1Poly.Polygraph.permutationToCrossingWord_one

-- the non-vacuity firings
#assert_no_axioms FX1Poly.Polygraph.isBoundaryInvolution_swapPair
#assert_no_axioms FX1Poly.Polygraph.capArcFeetIndices_mem_sound_adversarialB
#assert_no_axioms FX1Poly.Polygraph.cupArcTop_sub_exact_adversarialB

-- the honesty markers + the machine-checked r13 ledger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasArcEnumeration
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasArcConjugatorLeg
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasArcEnumerationConjugated
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r13Ledger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerMiddleR13Complete
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_r14Ledger
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerMiddleR14Complete

end FX1PolyAudit
