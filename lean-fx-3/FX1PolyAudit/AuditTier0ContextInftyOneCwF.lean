import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.InftyOneCwF

/-! # FX1PolyAudit/AuditTier0ContextInftyOneCwF — zero-axiom gate for context-14's (∞,1)-CwF

Per-declaration zero-axiom gate for `context-14`'s context-side deliverable
(`FX1Poly/Tier0/Context/InftyOneCwF.lean`): the Segal-space layer of an (∞,1)-category over
`context-13`'s simplicial site — edge/vertex maps, composable edges, the spine of a 2-simplex, the level-2
Segal condition (the (∞,1)-composition), and the point as a genuine Segal witness.  The nerve witness,
Rezk completeness, ∞-topos descent, the natural-model type families, and the univalent universe are the
honest deferrals (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The edge/vertex maps
#assert_no_axioms FX1Poly.Tier0.SimplexMap.edge01
#assert_no_axioms FX1Poly.Tier0.SimplexMap.edge12
#assert_no_axioms FX1Poly.Tier0.SimplexMap.vertexBot
#assert_no_axioms FX1Poly.Tier0.SimplexMap.vertexTop

-- Composable edges + the spine of a 2-simplex
#assert_no_axioms FX1Poly.Tier0.ComposableEdges
#assert_no_axioms FX1Poly.Tier0.SimplicialSet.spineOf

-- The level-2 Segal condition + the terminal Segal witness
#assert_no_axioms FX1Poly.Tier0.Segal2
#assert_no_axioms FX1Poly.Tier0.terminalSimplicialSet
#assert_no_axioms FX1Poly.Tier0.terminalSegal2

-- The (∞,1)-CwF datum + honesty markers + smoke
#assert_no_axioms FX1Poly.Tier0.InftyOneCwFData
#assert_no_axioms FX1Poly.Tier0.fxInftyOneCwF
#assert_no_axioms FX1Poly.Tier0.fxInftyOneCwF_hasNerveWitness
#assert_no_axioms FX1Poly.Tier0.fxInftyOneCwF_hasRezkCompleteness
#assert_no_axioms FX1Poly.Tier0.fxInftyOneCwF_hasInftyToposDescent
#assert_no_axioms FX1Poly.Tier0.fxInftyOneCwF_hasNaturalModelTypeFamilies
#assert_no_axioms FX1Poly.Tier0.fxInftyOneCwF_hasUnivalentUniverse
#assert_no_axioms FX1Poly.Tier0.terminalSegal2_fillSpine_smoke

end FX1PolyAudit
