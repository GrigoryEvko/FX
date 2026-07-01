import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.Confluence.DiamondConfluence

/-! # FX1PolyAudit.Polygraph.Rewriting.Confluence.DiamondConfluence

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.Rewriting.Confluence.DiamondConfluence`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The diamond-implies-confluence route (strip lemma), the second abstract confluence path complementing
-- Newman: confluence from the diamond property alone, no termination.  ReflTransClosure.monotone/collapse
-- (the sandwich glue) + DiamondProperty + stripLemma (single strips against many) + diamondConfluence +
-- confluentOfDiamondSimulation (the parallel-reduction recipe: rel subset parRel subset RTC rel + parRel
-- diamond implies rel confluent — the recipe the TABLE lane's ParStepOverTable discharges).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.ReflTransClosure.monotone

#assert_no_axioms FX1Poly.Core.ReflTransClosure.collapse

#assert_no_axioms FX1Poly.Core.DiamondProperty

#assert_no_axioms FX1Poly.Core.stripLemma

#assert_no_axioms FX1Poly.Core.diamondConfluenceAux

#assert_no_axioms FX1Poly.Core.diamondConfluence

#assert_no_axioms FX1Poly.Core.confluentOfDiamondSimulation

end FX1PolyAudit
