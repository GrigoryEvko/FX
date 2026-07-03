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

#assert_no_axioms FX1Poly.Polygraph.selfLoopBlocksAccessibility
#assert_no_axioms FX1Poly.Polygraph.adjunctionGodementSelfLoop
#assert_no_axioms FX1Poly.Polygraph.adjunctionGodementSelfLoopAtAnyPosition
#assert_no_axioms FX1Poly.Polygraph.adjunctionTraceReducerTerminatingRefuted
#assert_no_axioms FX1Poly.Polygraph.adjunctionTraceReducerWellFoundedRefuted
#assert_no_axioms FX1Poly.Polygraph.equationalTheoryAbsorb
#assert_no_axioms FX1Poly.Polygraph.spineTraceEquivIffOrientedTheory
#assert_no_axioms FX1Poly.Polygraph.adjunctionTraceDecisionViaOrientedReducer
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasConvergentGodementReducer

end FX1PolyAudit
