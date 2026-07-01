import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.Confluence.DecreasingDiagrams

/-! # FX1PolyAudit.Polygraph.Rewriting.Confluence.DecreasingDiagrams

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.Rewriting.Confluence.DecreasingDiagrams`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Decreasing diagrams: the universal confluence FRAMEWORK + the universality over the diamond
-- (DecreasingDiagrams.lean).  labeledUnion / labeledBelow (a Nat-labeled rewrite system) + LocallyDecreasing
-- (the sum-bounded valley condition) + diamondProperty_isLocallyDecreasing (the diamond is the degenerate
-- single-label decreasing diagram — the universality direction) + labeledUnion_diamond_isConfluent (the
-- framework recovers the diamond's confluence via diamondConfluence).  The full van Oostrom
-- LocallyDecreasing ⟹ Confluent theorem (multi-label, multiset induction) is the deferred capstone.
#assert_no_axioms FX1Poly.Core.labeledUnion

#assert_no_axioms FX1Poly.Core.labeledBelow

#assert_no_axioms FX1Poly.Core.labeledBelow.toUnion

#assert_no_axioms FX1Poly.Core.LocallyDecreasing

#assert_no_axioms FX1Poly.Core.diamondProperty_isLocallyDecreasing

#assert_no_axioms FX1Poly.Core.labeledUnion_diamond_isConfluent

-- The SINGLE-LABEL decreasing-diagrams theorem = Huet's strong confluence ⟹ confluence (a genuine sound
-- DD theorem, more than the diamond).  reflStep (→=) + StronglyConfluent + the SC strip lemma + the
-- confluence core + stronglyConfluent_implies_confluent (THE theorem) + diamondProperty_implies_stronglyConfluent
-- (the diamond is an SC instance, so diamondConfluence is a corollary) + stronglyConfluent_isLocallyDecreasing
-- (SC is the single-label decreasing diagram).  The multi-label van Oostrom theorem stays deferred.
#assert_no_axioms FX1Poly.Core.reflStep

#assert_no_axioms FX1Poly.Core.StronglyConfluent

#assert_no_axioms FX1Poly.Core.stronglyConfluent_strip

#assert_no_axioms FX1Poly.Core.stronglyConfluent_confluentAux

#assert_no_axioms FX1Poly.Core.stronglyConfluent_implies_confluent

#assert_no_axioms FX1Poly.Core.diamondProperty_implies_stronglyConfluent

#assert_no_axioms FX1Poly.Core.stronglyConfluent_isLocallyDecreasing

end FX1PolyAudit
