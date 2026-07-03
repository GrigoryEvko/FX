import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcReconstruction

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.ArcReconstruction — zero-axiom gate (mode-3 floor, planar-arc reconstruction)

Per-declaration zero-axiom gate for the COMBINATORIAL half of the Joyal-Street reconstruction (planar-isotopy
completeness, spine-modulo-trace): the abstract Mazurkiewicz connectivity engine (independence predicate,
adjacent-swap equivalence, the `bubbleFront` engine, the operational matching and its assembly), the concrete
Godement-closure head-extraction matching and its assembly into `SpineTraceEquiv`, the reconstruction theorems
GATED on the single geometric head-extraction residual, and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the parent does the unified registration). -/

namespace FX1PolyAudit

-- the abstract Mazurkiewicz connectivity engine (generic identity-preserving independence)
#assert_no_axioms FX1Poly.Polygraph.IndepAllWith
#assert_no_axioms FX1Poly.Polygraph.AdjacentSwapEquiv
#assert_no_axioms FX1Poly.Polygraph.AdjacentSwapEquiv.bubbleFront
#assert_no_axioms FX1Poly.Polygraph.TraceMatched
#assert_no_axioms FX1Poly.Polygraph.adjacentSwapEquiv_of_traceMatched

-- the head-extraction matching on the context-shifting Godement closure + its assembly
#assert_no_axioms FX1Poly.Polygraph.SpineTraceMatched
#assert_no_axioms FX1Poly.Polygraph.spineTraceEquiv_of_traceMatched

-- the reconstruction, GATED on the single geometric head-extraction residual
#assert_no_axioms FX1Poly.Polygraph.arcStructureReconstruction_spine_of_matching
#assert_no_axioms FX1Poly.Polygraph.arcStructureReconstruction_cell_of_matching

-- trace equivalence is length-preserving (the unconditional sound invariant the refutation rides)
#assert_no_axioms FX1Poly.Polygraph.SpineGodementStep.length_eq
#assert_no_axioms FX1Poly.Polygraph.SpineTraceEquiv.length_eq
#assert_no_axioms FX1Poly.Polygraph.SpineTraceMatched.length_eq

-- the structural-induction assembly: the matching from the per-step geometric inputs
#assert_no_axioms FX1Poly.Polygraph.SpineArcHeadExtraction
#assert_no_axioms FX1Poly.Polygraph.SpineArcNilInversion
#assert_no_axioms FX1Poly.Polygraph.spineTraceMatched_of_headExtraction

-- the literal spine-list residual is over-quantified — REFUTED (the witness defs are checked transitively here)
#assert_no_axioms FX1Poly.Polygraph.not_arcHeadExtractionMatching

-- the genuine (faithful-fragment) cell-level reconstruction residual + its wiring
#assert_no_axioms FX1Poly.Polygraph.ArcCellReconstruction
#assert_no_axioms FX1Poly.Polygraph.arcStructureReconstruction_cell_of_cellReconstruction

-- the cell-level reconstruction is FALSE at a general signature — REFUTED (witness cells checked transitively)
#assert_no_axioms FX1Poly.Polygraph.not_arcCellReconstruction

-- the generator-free base fragment of the reconstruction (unconditional, every signature)
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spine_eq_nil_of_generatorCount_zero
#assert_no_axioms FX1Poly.Polygraph.spineTraceEquiv_of_generatorFree

-- the cup/cap-SEED nil-inversion geometric input, discharged faithfully from the arc structure
-- (natAddFourMiddleExchange is private, checked transitively via adjunctionCupCapAtomCount_eq_length)
#assert_no_axioms FX1Poly.Polygraph.arcStructureOfSpineList_cupCount
#assert_no_axioms FX1Poly.Polygraph.arcStructureOfSpineList_capCount
#assert_no_axioms FX1Poly.Polygraph.adjunctionAtom_cupOrCap
#assert_no_axioms FX1Poly.Polygraph.adjunctionCupCapAtomCount_eq_length
#assert_no_axioms FX1Poly.Polygraph.spineArcNilInversion_adjunction

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcReconstructionConnectivityEngine
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcHeadExtractionMatching
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcStructureReconstructionAssembled
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineTraceLengthInvariant
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcHeadExtractionTraceAssembly
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcHeadExtractionMatchingRefuted
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCellReconstructionRefutedAtGeneralSignature
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasGeneratorFreeReconstruction
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSeedNilInversionDischarged
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCellReconstruction

end FX1PolyAudit
