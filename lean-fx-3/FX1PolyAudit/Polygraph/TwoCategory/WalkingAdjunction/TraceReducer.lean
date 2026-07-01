import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.TraceReducer

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.TraceReducer — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the trace-decision REFUTATION + corrected harness: the proof that the full
positionwise Godement step is reflexive (`adjunctionGodementSelfLoop{,AtAnyPosition}`) hence its strong
normalization is provably `False` (`selfLoopBlocksAccessibility`, `adjunctionTraceReducerTerminating/WellFounded
Refuted`), and the corrected `adjunctionTraceDecisionViaOrientedReducer` over an ORIENTED sub-relation
(`equationalTheoryAbsorb`, `spineTraceEquivIffOrientedTheory`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.selfLoopBlocksAccessibility
#assert_no_axioms FX1Poly.Tier0.adjunctionGodementSelfLoop
#assert_no_axioms FX1Poly.Tier0.adjunctionGodementSelfLoopAtAnyPosition
#assert_no_axioms FX1Poly.Tier0.adjunctionTraceReducerTerminatingRefuted
#assert_no_axioms FX1Poly.Tier0.adjunctionTraceReducerWellFoundedRefuted
#assert_no_axioms FX1Poly.Tier0.equationalTheoryAbsorb
#assert_no_axioms FX1Poly.Tier0.spineTraceEquivIffOrientedTheory
#assert_no_axioms FX1Poly.Tier0.adjunctionTraceDecisionViaOrientedReducer
#assert_no_axioms FX1Poly.Tier0.fxMode_hasConvergentGodementReducer

end FX1PolyAudit
