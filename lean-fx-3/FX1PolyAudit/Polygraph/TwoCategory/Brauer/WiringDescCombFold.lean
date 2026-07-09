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

-- B2: the commuteBlock helper + the C4 carry crux (private carryIntoRun + arithmetic covered transitively)
#assert_no_axioms FX1Poly.Polygraph.commuteLetterPastBlock
#assert_no_axioms FX1Poly.Polygraph.combCase_carry

-- B3: the comb state, the six-case single-letter insertion, the fold, and THE COMB THEOREM
#assert_no_axioms FX1Poly.Polygraph.combWord
#assert_no_axioms FX1Poly.Polygraph.combInsert_step
#assert_no_axioms FX1Poly.Polygraph.comb_fold_from
#assert_no_axioms FX1Poly.Polygraph.comb_straightens

-- B4: the computable comb normal form + non-vacuity on the r9 stuck word + a clean word
#assert_no_axioms FX1Poly.Polygraph.combInsertData
#assert_no_axioms FX1Poly.Polygraph.combNormalizeForm
#assert_no_axioms FX1Poly.Polygraph.combNormalizeForm_stuck_word
#assert_no_axioms FX1Poly.Polygraph.comb_dissolves_stuck_word
#assert_no_axioms FX1Poly.Polygraph.comb_straightens_stuck_word
#assert_no_axioms FX1Poly.Polygraph.combNormalizeForm_clean_word
#assert_no_axioms FX1Poly.Polygraph.comb_straightens_clean_word

-- B5: the honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCombFold

end FX1PolyAudit
