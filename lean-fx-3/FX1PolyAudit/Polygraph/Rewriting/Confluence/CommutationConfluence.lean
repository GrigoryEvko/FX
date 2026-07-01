import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.Confluence.CommutationConfluence

/-! # FX1PolyAudit.Polygraph.Rewriting.Confluence.CommutationConfluence

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.Rewriting.Confluence.CommutationConfluence`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Hindley-Rosen via the diamond (abstract toolkit): the third confluence route after Newman (terminating)
-- and DiamondConfluence (single diamond).  Modular: it combines two separately-confluent relations whose
-- diamonds commute into a confluent union (the intended FX use: beta-parallel diamond + iota-parallel diamond +
-- beta/iota commute, without one monolithic 20-arm ParStep).  StronglyCommutes + DiamondProperty.union (4-way
-- case split) + confluentOfUnionDiamonds + confluentUnionOfParallelDiamonds (the two-relation generalization of
-- confluentOfDiamondSimulation).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.StronglyCommutes

#assert_no_axioms FX1Poly.Core.DiamondProperty.union

#assert_no_axioms FX1Poly.Core.confluentOfUnionDiamonds

#assert_no_axioms FX1Poly.Core.confluentUnionOfParallelDiamonds

end FX1PolyAudit
