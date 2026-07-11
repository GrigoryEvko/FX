import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcConjugator

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcConjugator — zero-axiom gate (BRAUER-MIDDLE r14 T-ENUM E2)

Per-declaration zero-axiom gate for the conjugator-correctness leg (E2) of T-ENUM: the validity gate
(`IsPermutationOfRange`), the general selection-sort roundtrip
(`permuteOfCrossingWord_permutationToCrossingWord`), and the honesty marker.  The roundtrip assertion transitively
covers every re-derived private helper (the `propext`-free `Nat.sub` / range / map / membership kit, the
descending-run bridge, the placement / prefix-stability lemmas, and the invariant induction).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the validity gate + the general roundtrip theorem
#assert_no_axioms FX1Poly.Polygraph.IsPermutationOfRange
#assert_no_axioms FX1Poly.Polygraph.permuteOfCrossingWord_permutationToCrossingWord

-- the honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasConjugatorRoundtrip

-- BRAUER r21 B1: the staircase position-bound (`∀ pos ∈ staircase, pos + 2 ≤ width`) + its concrete-output probe
#assert_no_axioms FX1Poly.Polygraph.permutationToCrossingWord_posBound_probe
#assert_no_axioms FX1Poly.Polygraph.permutationToCrossingWord_posBound
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStaircasePositionBound

end FX1PolyAudit
