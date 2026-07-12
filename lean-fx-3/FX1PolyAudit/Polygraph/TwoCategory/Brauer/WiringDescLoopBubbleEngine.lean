import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescLoopBubbleEngine

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescLoopBubbleEngine — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER r41 J-loop engine lemma: the `cupPos`-generic loop-count computation
(`loopBubbleProcessLoops` / `loopBubbleLoopsEqOne`), the generic loop non-emptiness (`loopBubbleNotEmpty`), the total
loop-outcome builder (`outcomeLoopAtFactoredTotal` / `outcomeLoopAtFactoredTotal_fate`), the honesty marker, and the
machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the structural `cupPos`
cases over `stepCup` / `stepCap` / `extractDiagram`, the `Nat.noConfusion` emptiness refutation (never
`Nat.succ_ne_zero`, which leaks `propext`), and the `rfl` pins are all axiom-free.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.loopBubbleProcessLoops
#assert_no_axioms FX1Poly.Polygraph.loopBubbleLoopsEqOne
#assert_no_axioms FX1Poly.Polygraph.loopBubbleNotEmpty
#assert_no_axioms FX1Poly.Polygraph.outcomeLoopAtFactoredTotal
#assert_no_axioms FX1Poly.Polygraph.outcomeLoopAtFactoredTotal_fate
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasLoopBubbleEngineLemma
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_loopBubbleEngineTerminalState

-- Independent cross-check (mandatory, per the AuditAll zero-axiom protocol): the headline declarations print no axioms.
#print axioms FX1Poly.Polygraph.loopBubbleProcessLoops
#print axioms FX1Poly.Polygraph.loopBubbleNotEmpty
#print axioms FX1Poly.Polygraph.outcomeLoopAtFactoredTotal
#print axioms FX1Poly.Polygraph.fxBrauer_loopBubbleEngineTerminalState

end FX1PolyAudit
