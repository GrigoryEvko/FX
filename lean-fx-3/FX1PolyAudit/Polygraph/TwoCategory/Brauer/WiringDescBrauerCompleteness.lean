import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerCompleteness

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBrauerCompleteness — zero-axiom gate (BREACH r3)

Per-declaration zero-axiom gate for the BREACH r3 pieces: the cellular standard-form datatype + word realization +
evals (P1), and the stabilizer-generator = untwist identification (P3a, diagram-preserving foot-swaps +
convertibility re-exports).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- P1: the cellular standard-form datatype + word realization + length lemmas + evals
#assert_no_axioms FX1Poly.Polygraph.capWord
#assert_no_axioms FX1Poly.Polygraph.cupWord
#assert_no_axioms FX1Poly.Polygraph.standardFormWord
#assert_no_axioms FX1Poly.Polygraph.standardFormDiagram
#assert_no_axioms FX1Poly.Polygraph.capWord_length
#assert_no_axioms FX1Poly.Polygraph.cupWord_length
#assert_no_axioms FX1Poly.Polygraph.standardFormWord_empty_two
#assert_no_axioms FX1Poly.Polygraph.standardFormWord_crossing_two
#assert_no_axioms FX1Poly.Polygraph.standardFormWord_capCup_two
#assert_no_axioms FX1Poly.Polygraph.standardFormWord_concat

-- P3a: the stabilizer generator = untwist identification
#assert_no_axioms FX1Poly.Polygraph.cupFootSwap_preserves_diagram
#assert_no_axioms FX1Poly.Polygraph.capFootSwap_preserves_diagram
#assert_no_axioms FX1Poly.Polygraph.cupFootSwap_conv
#assert_no_axioms FX1Poly.Polygraph.capFootSwap_conv
#assert_no_axioms FX1Poly.Polygraph.cupFootSwap_preserves_diagram_smoke

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCellularStandardFormDatatype
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStabilizerGeneratorIsUntwist

end FX1PolyAudit
