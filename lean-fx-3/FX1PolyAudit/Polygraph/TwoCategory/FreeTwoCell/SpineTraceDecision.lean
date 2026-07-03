import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.SpineTraceDecision — zero-axiom gate (mode-3 floor, full planar-arc route)

Per-declaration zero-axiom gate for the FREE 2-cell decision via the FULL planar-arc structure (Joyal-Street,
spine-modulo-trace): the arc-structure type + its computing `DecidableEq`, the event-tracking union-find fold
`arcStructureOf`, the structural-and-whisker soundness, the Godement-reduced full soundness, the UNCONDITIONAL
cup/cap-count `TwoCellConvFull` invariants, the snake-gap-closing CRUX (arc structure separates the snake, the
identity, and the double snake — fixing the matching route's decision-vacuity), the interchange-obstruction
count smokes, and the GATED decidability of `SpineTraceEquiv` / `TwoCellConvFull`.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the parent does the unified registration). -/

namespace FX1PolyAudit

-- the full planar-arc type + its computing decidable equality
#assert_no_axioms FX1Poly.Polygraph.FullArcStructure
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqFullArcStructure
#assert_no_axioms FX1Poly.Polygraph.ArcWireState

-- the event-tracking union-find fold + extraction
#assert_no_axioms FX1Poly.Polygraph.stepCupArc
#assert_no_axioms FX1Poly.Polygraph.stepCapArc
#assert_no_axioms FX1Poly.Polygraph.stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.processArcSpine
#assert_no_axioms FX1Poly.Polygraph.countEventsInRoot
#assert_no_axioms FX1Poly.Polygraph.internalEventCountAt
#assert_no_axioms FX1Poly.Polygraph.extractArc
#assert_no_axioms FX1Poly.Polygraph.arcStructureOfSpineList
#assert_no_axioms FX1Poly.Polygraph.arcStructureOf

-- soundness under the interchange-free structural fragment + whisker functoriality
#assert_no_axioms FX1Poly.Polygraph.arcStructureOf_congr_of_spine_eq
#assert_no_axioms FX1Poly.Polygraph.arcStructureOf_eq_of_interchangeFreeStep
#assert_no_axioms FX1Poly.Polygraph.arcStructureOf_whiskerLeftUnit
#assert_no_axioms FX1Poly.Polygraph.arcStructureOf_whiskerRightUnit
#assert_no_axioms FX1Poly.Polygraph.arcStructureOf_whiskerLeftComp
#assert_no_axioms FX1Poly.Polygraph.arcStructureOf_whiskerRightComp

-- FULL TwoCellConvFull soundness, assembled modulo the single Godement residual
#assert_no_axioms FX1Poly.Polygraph.extractArcAfterProcessing
#assert_no_axioms FX1Poly.Polygraph.arcTraceInvariant_of_godementInvariant
#assert_no_axioms FX1Poly.Polygraph.arcStructureOf_sound_of_godementInvariant

-- the cup/cap counts are UNCONDITIONAL TwoCellConvFull invariants (the unconditional snake separator)
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.cupCount
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.capCount
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.cupCount_castBoundary
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.capCount_castBoundary
#assert_no_axioms FX1Poly.Polygraph.TwoCellStep.cupCount_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellStep.capCount_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.cupCount_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.capCount_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellConvFull.cupCount_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellConvFull.capCount_eq

-- ★ the CRUX: the arc structure separates the snake, the identity, and the double snake
#assert_no_axioms FX1Poly.Polygraph.snake_arcStructureOf
#assert_no_axioms FX1Poly.Polygraph.identityOnLeft_arcStructureOf
#assert_no_axioms FX1Poly.Polygraph.snake_arcStructureOf_cupCount
#assert_no_axioms FX1Poly.Polygraph.identityOnLeft_arcStructureOf_cupCount
#assert_no_axioms FX1Poly.Polygraph.snake_internalCupCounts
#assert_no_axioms FX1Poly.Polygraph.identityOnLeft_internalCupCounts
#assert_no_axioms FX1Poly.Polygraph.snake_internalCupCounts_ne_identity
#assert_no_axioms FX1Poly.Polygraph.snake_arcStructureOf_ne_identity
#assert_no_axioms FX1Poly.Polygraph.doubleSnake_arcStructureOf
#assert_no_axioms FX1Poly.Polygraph.doubleSnake_arcStructureOf_cupCount
#assert_no_axioms FX1Poly.Polygraph.arcStructure_separates_at_seed

-- the interchange-obstruction count smokes (unconditional)
#assert_no_axioms FX1Poly.Polygraph.parallelUnits_cupCount_eq
#assert_no_axioms FX1Poly.Polygraph.parallelUnits_capCount_eq
#assert_no_axioms FX1Poly.Polygraph.parallelCounits_capCount_eq
#assert_no_axioms FX1Poly.Polygraph.parallelCounits_cupCount_eq

-- the GATED decision (trace-invariance reduction + the two decidability interfaces)
#assert_no_axioms FX1Poly.Polygraph.arcStructureOfSpineList_traceInvariant
#assert_no_axioms FX1Poly.Polygraph.decidableSpineTraceEquiv_of
#assert_no_axioms FX1Poly.Polygraph.decidableTwoCellConvFull_of

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcStructureClosesSnakeGap
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcGodementIndependenceProof
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcStructureReconstruction
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCompleteArcDecision

end FX1PolyAudit
