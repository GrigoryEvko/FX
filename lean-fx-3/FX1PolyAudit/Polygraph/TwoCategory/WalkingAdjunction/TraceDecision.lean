import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.TraceDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.TraceDecision — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the trace word problem wired to the convergent-reducer decision engine: the
carrier `DecidableEq` (spine atoms and lists) and its `rfl`-computing smokes, the positionwise Godement step
with the `SpineTraceEquiv` ⟷ `EquationalTheory` bridge, the single-transposition soundness core, and the
end-to-end engine wiring + assembly hook.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineAtomDecEq
#assert_no_axioms FX1Poly.Polygraph.adjunctionSpineAtomDecEq
#assert_no_axioms FX1Poly.Polygraph.adjunctionSpineListDecEq
#assert_no_axioms FX1Poly.Polygraph.unitSpine_eq_self_decidably
#assert_no_axioms FX1Poly.Polygraph.unitSpine_ne_idSpine_decidably
#assert_no_axioms FX1Poly.Polygraph.SpineGodementAtAnyPosition
#assert_no_axioms FX1Poly.Polygraph.SpineGodementAtAnyPosition.toSpineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.equationalTheory_consCongr
#assert_no_axioms FX1Poly.Polygraph.spineTraceEquiv_iff_equationalTheory
#assert_no_axioms FX1Poly.Polygraph.singleAtomGodementStep
#assert_no_axioms FX1Poly.Polygraph.singleAtomTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.adjunctionTraceDecisionOfReducer
#assert_no_axioms FX1Poly.Polygraph.adjunctionTwoCellWordProblemViaGodementReducer
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineTraceDecision

end FX1PolyAudit
