import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Frobenius.PartitionModel

/-! # FX1PolyAudit.Polygraph.TwoCategory.Frobenius.PartitionModel — zero-axiom gate (WP-FROB r1, FROB-2)

Per-declaration zero-axiom gate for the special-commutative-Frobenius spider PARTITION engine: the diagram carrier
(`SpiderDiagramType` / `SpiderPartitionType` + the closed-count-forgetting projection), the four generator wirings
(`μ` / `δ` / `η` / `ε`) and their atoms, the partition + closed-component extractor, the spider diagram evaluators,
and the engine smokes (arbitrary-size blocks, the closed-component counter firing, the special-bubble/Brauer-loops
delta, the crossing transposition).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- FROB-2: the spider carrier + the extraspecial projection
#assert_no_axioms FX1Poly.Polygraph.SpiderDiagramType
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqSpiderDiagramType
#assert_no_axioms FX1Poly.Polygraph.SpiderPartitionType
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqSpiderPartitionType
#assert_no_axioms FX1Poly.Polygraph.forgetSpiderClosed

-- FROB-2: the per-generator spider wirings + atoms
#assert_no_axioms FX1Poly.Polygraph.multWiring
#assert_no_axioms FX1Poly.Polygraph.comultWiring
#assert_no_axioms FX1Poly.Polygraph.unitWiring
#assert_no_axioms FX1Poly.Polygraph.counitWiring
#assert_no_axioms FX1Poly.Polygraph.multAt
#assert_no_axioms FX1Poly.Polygraph.comultAt
#assert_no_axioms FX1Poly.Polygraph.unitAt
#assert_no_axioms FX1Poly.Polygraph.counitAt

-- FROB-2: the partition + closed-component extractor
#assert_no_axioms FX1Poly.Polygraph.firstIndexWithRoot
#assert_no_axioms FX1Poly.Polygraph.natListRootEqAny
#assert_no_axioms FX1Poly.Polygraph.closedComponentCount
#assert_no_axioms FX1Poly.Polygraph.extractSpiderDiagram
#assert_no_axioms FX1Poly.Polygraph.spiderDiagramOf
#assert_no_axioms FX1Poly.Polygraph.extraSpiderDiagramOf

-- FROB-2: the engine smokes
#assert_no_axioms FX1Poly.Polygraph.mult_spiderDiagram
#assert_no_axioms FX1Poly.Polygraph.identityPair_spiderDiagram
#assert_no_axioms FX1Poly.Polygraph.mult_ne_identityPair
#assert_no_axioms FX1Poly.Polygraph.bone_closedComponents_one
#assert_no_axioms FX1Poly.Polygraph.specialBubble_uncounted
#assert_no_axioms FX1Poly.Polygraph.crossing_spiderDiagram

-- FROB-2: the honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderWiringEngine
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasPartitionModel
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasPartitionInvariant
#assert_no_axioms FX1Poly.Polygraph.fxFrob_has2CobGenus

end FX1PolyAudit
