import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FreeTwoCellTraceDecision

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellTraceDecision — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the trace word problem wired to the convergent-reducer decision engine: the
carrier `DecidableEq` (spine atoms and lists) and its `rfl`-computing smokes, the positionwise Godement step
with the `SpineTraceEquiv` ⟷ `EquationalTheory` bridge, the single-transposition soundness core, and the
end-to-end engine wiring + assembly hook.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.spineAtomDecEq
#assert_no_axioms FX1Poly.Tier0.adjunctionSpineAtomDecEq
#assert_no_axioms FX1Poly.Tier0.adjunctionSpineListDecEq
#assert_no_axioms FX1Poly.Tier0.unitSpine_eq_self_decidably
#assert_no_axioms FX1Poly.Tier0.unitSpine_ne_idSpine_decidably
#assert_no_axioms FX1Poly.Tier0.SpineGodementAtAnyPosition
#assert_no_axioms FX1Poly.Tier0.SpineGodementAtAnyPosition.toSpineTraceEquiv
#assert_no_axioms FX1Poly.Tier0.equationalTheory_consCongr
#assert_no_axioms FX1Poly.Tier0.spineTraceEquiv_iff_equationalTheory
#assert_no_axioms FX1Poly.Tier0.singleAtomGodementStep
#assert_no_axioms FX1Poly.Tier0.singleAtomTraceEquiv
#assert_no_axioms FX1Poly.Tier0.adjunctionTraceDecisionOfReducer
#assert_no_axioms FX1Poly.Tier0.adjunctionTwoCellWordProblemViaGodementReducer
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSpineTraceDecision

end FX1PolyAudit
