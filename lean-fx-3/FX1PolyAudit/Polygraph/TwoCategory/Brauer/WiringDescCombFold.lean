import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCombFold

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCombFold — zero-axiom gate (WP-BRAUER-4 r6)

Per-declaration zero-axiom gate for the comb fold (the Coxeter–Moser coset factorization): the run datatype +
invariant predicates, the `commuteBlock` helper, and the six comb case lemmas (the C4 carry crux first), the fold,
and the non-vacuity smokes.  The private structural helpers are covered transitively.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- B1: the run datatype + invariant predicates
#assert_no_axioms FX1Poly.Polygraph.descendingPositions
#assert_no_axioms FX1Poly.Polygraph.mentionsOnlyBelow
#assert_no_axioms FX1Poly.Polygraph.AllDistantFrom

-- B2: the commuteBlock helper + the C4 carry crux
#assert_no_axioms FX1Poly.Polygraph.commuteLetterPastBlock
#assert_no_axioms FX1Poly.Polygraph.combCase_carry

end FX1PolyAudit
