import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.BareConvDecisionReconciliation

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.BareConvDecisionReconciliation — zero-axiom gate

Per-declaration zero-axiom gate for the flag-B r7 TERMINAL reconciliation of `fxMode_hasModeRelativeConvDecision`:
the decisive strict-finer separation (`bareConvStrictlyFinerThanFaithfulDecided` — the Godement pair is
`TwoCellConvFull` yet NOT bare `TwoCellConv`), the reconciliation record and its inhabitant bundling the four
already-audited shipped legs (`BareConvDecisionReconciliation`, `bareConvDecisionReconciliation`), and the honesty
marker (`fxMode_hasBareConvDecisionDeepWall`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.bareConvStrictlyFinerThanFaithfulDecided
#assert_no_axioms FX1Poly.Polygraph.bareConvDecisionReconciliation
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasBareConvDecisionDeepWall

end FX1PolyAudit
