import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision — zero-axiom gate (mode-3 floor, matching route)

Per-declaration zero-axiom gate for the Joyal–Street MATCHING decision of the FREE 2-cell word problem: the
topological type + its computing `DecidableEq`, the union-find reading `matchingOf`, the structural-fragment
soundness, the generator-count `TwoCellConvFull` invariant (the snake separator), and the CRUX obstruction
smokes (interchange + counit endpoints matched EQUAL) plus the snake-gap incompleteness witness.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the parent does the unified registration). -/

namespace FX1PolyAudit

-- the topological type + its computing decidable equality
#assert_no_axioms FX1Poly.Polygraph.DiagramType
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqDiagramType

-- list / union-find / state machinery
#assert_no_axioms FX1Poly.Polygraph.natListGetAt
#assert_no_axioms FX1Poly.Polygraph.natListInsertAt
#assert_no_axioms FX1Poly.Polygraph.natListRemoveTwoAt
#assert_no_axioms FX1Poly.Polygraph.unionFindParent
#assert_no_axioms FX1Poly.Polygraph.unionFindRoot
#assert_no_axioms FX1Poly.Polygraph.unionFindRootOf
#assert_no_axioms FX1Poly.Polygraph.isSameComponent
#assert_no_axioms FX1Poly.Polygraph.unionFindJoin
#assert_no_axioms FX1Poly.Polygraph.stepCup
#assert_no_axioms FX1Poly.Polygraph.stepCap
#assert_no_axioms FX1Poly.Polygraph.stepAtom
#assert_no_axioms FX1Poly.Polygraph.processSpine
#assert_no_axioms FX1Poly.Polygraph.findPartnerScan
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf
#assert_no_axioms FX1Poly.Polygraph.extractDiagram
#assert_no_axioms FX1Poly.Polygraph.matchingOfSpineList
#assert_no_axioms FX1Poly.Polygraph.matchingOf

-- soundness under the interchange-free structural fragment + whisker functoriality
-- (every TwoCellConvFull generator except the single interchange step)
#assert_no_axioms FX1Poly.Polygraph.matchingOf_congr_of_spine_eq
#assert_no_axioms FX1Poly.Polygraph.matchingOf_eq_of_interchangeFreeStep
#assert_no_axioms FX1Poly.Polygraph.matchingOf_whiskerLeftUnit
#assert_no_axioms FX1Poly.Polygraph.matchingOf_whiskerRightUnit
#assert_no_axioms FX1Poly.Polygraph.matchingOf_whiskerLeftComp
#assert_no_axioms FX1Poly.Polygraph.matchingOf_whiskerRightComp

-- FULL TwoCellConvFull soundness, assembled modulo exactly one named residual
#assert_no_axioms FX1Poly.Polygraph.extractAfterProcessing
#assert_no_axioms FX1Poly.Polygraph.traceInvariant_of_godementInvariant
#assert_no_axioms FX1Poly.Polygraph.matchingOf_sound_of_godementInvariant

-- generator count is a TwoCellConvFull invariant (the snake separator)
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.generatorCount_castBoundary
#assert_no_axioms FX1Poly.Polygraph.TwoCellConvFull.generatorCount_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellConvFull.not_of_generatorCount_ne

-- ★ the crux: the obstruction endpoints are matchingOf-EQUAL
#assert_no_axioms FX1Poly.Polygraph.parallelUnitsConvFull
#assert_no_axioms FX1Poly.Polygraph.parallelUnitsRedex_matchingOf
#assert_no_axioms FX1Poly.Polygraph.parallelUnitsReduct_matchingOf
#assert_no_axioms FX1Poly.Polygraph.parallelUnits_matchingOf_eq
#assert_no_axioms FX1Poly.Polygraph.parallelCounitsConvFull
#assert_no_axioms FX1Poly.Polygraph.parallelCounitsRedex_matchingOf
#assert_no_axioms FX1Poly.Polygraph.parallelCounitsReduct_matchingOf
#assert_no_axioms FX1Poly.Polygraph.parallelCounits_matchingOf_eq

-- the snake gap: sound but PROVABLY incomplete + decision-vacuous at the seed
#assert_no_axioms FX1Poly.Polygraph.snake_matchingOf
#assert_no_axioms FX1Poly.Polygraph.identityOnLeft_matchingOf
#assert_no_axioms FX1Poly.Polygraph.snake_matchingOf_eq_identity
#assert_no_axioms FX1Poly.Polygraph.snake_generatorCount_ne_identity
#assert_no_axioms FX1Poly.Polygraph.snake_not_convFull_identity
#assert_no_axioms FX1Poly.Polygraph.doubleSnake_matchingOf
#assert_no_axioms FX1Poly.Polygraph.decisionVacuity_at_seed
#assert_no_axioms FX1Poly.Polygraph.unit_counit_matchingOf

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCompleteMatchingInvariant
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingDecisionPowerAtSeed
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingGodementIndependenceProof

end FX1PolyAudit
