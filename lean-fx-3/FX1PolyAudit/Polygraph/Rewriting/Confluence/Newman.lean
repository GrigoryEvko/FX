import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.Confluence.Newman

/-! # FX1PolyAudit.Polygraph.Rewriting.Confluence.Newman

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.Rewriting.Confluence.Newman`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The abstract Newman's lemma: terminating + weakly confluent implies confluent, the confluence analogue of
-- the termination orders, generic over any relation.  ReflTransClosure (an own RTC, since
-- Relation.ReflTransGen is Mathlib-only) + single/trans; Joinable/WeaklyConfluent/Confluent vocabulary;
-- newmanAux is the WF-induction tiling (WCR on the two first steps, IH at each reduct, compose); newman is the
-- headline.  Zero-axiom: cases on RTC is propext-clean since its indices are free vars, not ctor patterns.
#assert_no_axioms FX1Poly.Core.ReflTransClosure

#assert_no_axioms FX1Poly.Core.ReflTransClosure.single

#assert_no_axioms FX1Poly.Core.ReflTransClosure.trans

#assert_no_axioms FX1Poly.Core.Joinable

#assert_no_axioms FX1Poly.Core.WeaklyConfluent

#assert_no_axioms FX1Poly.Core.Confluent

#assert_no_axioms FX1Poly.Core.newmanAux

#assert_no_axioms FX1Poly.Core.newman

-- The guarded twins: newmanGuardedAux/newmanGuarded thread a hereditary `guard` predicate so weak
-- confluence is only consumed where it holds (the typed beta-eta annotation-joinability fragment),
-- with per-source Acc rather than global WellFounded.  Same propext-clean RTC cases as newmanAux.
#assert_no_axioms FX1Poly.Core.newmanGuardedAux

#assert_no_axioms FX1Poly.Core.newmanGuarded

end FX1PolyAudit
