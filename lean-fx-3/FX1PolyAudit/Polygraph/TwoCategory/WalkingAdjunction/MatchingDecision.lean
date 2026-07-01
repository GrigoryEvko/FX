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
#assert_no_axioms FX1Poly.Tier0.DiagramType
#assert_no_axioms FX1Poly.Tier0.instDecidableEqDiagramType

-- list / union-find / state machinery
#assert_no_axioms FX1Poly.Tier0.natListGetAt
#assert_no_axioms FX1Poly.Tier0.natListInsertAt
#assert_no_axioms FX1Poly.Tier0.natListRemoveTwoAt
#assert_no_axioms FX1Poly.Tier0.unionFindParent
#assert_no_axioms FX1Poly.Tier0.unionFindRoot
#assert_no_axioms FX1Poly.Tier0.unionFindRootOf
#assert_no_axioms FX1Poly.Tier0.isSameComponent
#assert_no_axioms FX1Poly.Tier0.unionFindJoin
#assert_no_axioms FX1Poly.Tier0.stepCup
#assert_no_axioms FX1Poly.Tier0.stepCap
#assert_no_axioms FX1Poly.Tier0.stepAtom
#assert_no_axioms FX1Poly.Tier0.processSpine
#assert_no_axioms FX1Poly.Tier0.findPartnerScan
#assert_no_axioms FX1Poly.Tier0.partnerIndexOf
#assert_no_axioms FX1Poly.Tier0.extractDiagram
#assert_no_axioms FX1Poly.Tier0.matchingOfSpineList
#assert_no_axioms FX1Poly.Tier0.matchingOf

-- soundness under the interchange-free structural fragment + whisker functoriality
-- (every TwoCellConvFull generator except the single interchange step)
#assert_no_axioms FX1Poly.Tier0.matchingOf_congr_of_spine_eq
#assert_no_axioms FX1Poly.Tier0.matchingOf_eq_of_interchangeFreeStep
#assert_no_axioms FX1Poly.Tier0.matchingOf_whiskerLeftUnit
#assert_no_axioms FX1Poly.Tier0.matchingOf_whiskerRightUnit
#assert_no_axioms FX1Poly.Tier0.matchingOf_whiskerLeftComp
#assert_no_axioms FX1Poly.Tier0.matchingOf_whiskerRightComp

-- FULL TwoCellConvFull soundness, assembled modulo exactly one named residual
#assert_no_axioms FX1Poly.Tier0.extractAfterProcessing
#assert_no_axioms FX1Poly.Tier0.traceInvariant_of_godementInvariant
#assert_no_axioms FX1Poly.Tier0.matchingOf_sound_of_godementInvariant

-- generator count is a TwoCellConvFull invariant (the snake separator)
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.generatorCount_castBoundary
#assert_no_axioms FX1Poly.Tier0.TwoCellConvFull.generatorCount_eq
#assert_no_axioms FX1Poly.Tier0.TwoCellConvFull.not_of_generatorCount_ne

-- ★ the crux: the obstruction endpoints are matchingOf-EQUAL
#assert_no_axioms FX1Poly.Tier0.parallelUnitsConvFull
#assert_no_axioms FX1Poly.Tier0.parallelUnitsRedex_matchingOf
#assert_no_axioms FX1Poly.Tier0.parallelUnitsReduct_matchingOf
#assert_no_axioms FX1Poly.Tier0.parallelUnits_matchingOf_eq
#assert_no_axioms FX1Poly.Tier0.parallelCounitsConvFull
#assert_no_axioms FX1Poly.Tier0.parallelCounitsRedex_matchingOf
#assert_no_axioms FX1Poly.Tier0.parallelCounitsReduct_matchingOf
#assert_no_axioms FX1Poly.Tier0.parallelCounits_matchingOf_eq

-- the snake gap: sound but PROVABLY incomplete + decision-vacuous at the seed
#assert_no_axioms FX1Poly.Tier0.snake_matchingOf
#assert_no_axioms FX1Poly.Tier0.identityOnLeft_matchingOf
#assert_no_axioms FX1Poly.Tier0.snake_matchingOf_eq_identity
#assert_no_axioms FX1Poly.Tier0.snake_generatorCount_ne_identity
#assert_no_axioms FX1Poly.Tier0.snake_not_convFull_identity
#assert_no_axioms FX1Poly.Tier0.doubleSnake_matchingOf
#assert_no_axioms FX1Poly.Tier0.decisionVacuity_at_seed
#assert_no_axioms FX1Poly.Tier0.unit_counit_matchingOf

-- honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCompleteMatchingInvariant
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingDecisionPowerAtSeed
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingGodementIndependenceProof

end FX1PolyAudit
