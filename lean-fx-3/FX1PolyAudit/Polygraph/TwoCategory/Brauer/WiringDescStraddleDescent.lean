import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStraddleDescent

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescStraddleDescent — zero-axiom gate (BRAUER-MIDDLE r2, B2)

Per-declaration zero-axiom gate for the `straddleCount` primary coordinate and the lex measure that descends on the
straddle: the primary coordinate (`straddleCount`), the straddle primary descent (`straddleCount_straddle_lt`) and
the distant-move holds (`straddleCount_distant*_held`), the lex measure (`straddleLexMeasure`) with its combine lemmas
(`straddleLex_lt_of_primary` / `straddleLex_lt_of_secondary`), the full per-move lex descent table
(`straddleLex_straddle_lt` + `straddleLex_distant*_lt`), the non-vacuity bundle
(`straddle_lex_descends_where_arcMeasure_ascends`), and the two honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.straddleCount
#assert_no_axioms FX1Poly.Polygraph.straddleCount_straddle_lhs
#assert_no_axioms FX1Poly.Polygraph.straddleCount_straddle_rhs
#assert_no_axioms FX1Poly.Polygraph.straddleCount_straddle_lt
#assert_no_axioms FX1Poly.Polygraph.straddleCount_distantCupCap_held
#assert_no_axioms FX1Poly.Polygraph.straddleCount_distantCupCrossing_held
#assert_no_axioms FX1Poly.Polygraph.straddleCount_distantCupCup_held
#assert_no_axioms FX1Poly.Polygraph.straddleLexMeasure
#assert_no_axioms FX1Poly.Polygraph.straddleLex_lt_of_primary
#assert_no_axioms FX1Poly.Polygraph.straddleLex_lt_of_secondary
#assert_no_axioms FX1Poly.Polygraph.straddleLex_straddle_lt
#assert_no_axioms FX1Poly.Polygraph.straddleLex_distantCupCap_lt
#assert_no_axioms FX1Poly.Polygraph.straddleLex_distantCupCrossing_lt
#assert_no_axioms FX1Poly.Polygraph.straddleLex_distantCupCup_lt
#assert_no_axioms FX1Poly.Polygraph.straddle_lex_descends_where_arcMeasure_ascends
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStraddleLexDescent
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStraddleGlobalFuel

end FX1PolyAudit
