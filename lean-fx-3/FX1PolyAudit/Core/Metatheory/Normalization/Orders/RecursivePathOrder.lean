import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.Orders.RecursivePathOrder

/-! # FX1PolyAudit.Core.Metatheory.Normalization.Orders.RecursivePathOrder

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.Orders.RecursivePathOrder`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The RPO termination certificate: precedence times argument-order, lexicographically.  LexPair is the lex
-- product of two relations as a disjunction (not the indexed Prod.Lex, whose cases leaks propext via the
-- pair-index); isWellFounded by nested Acc with rcases on the Or.  wellFounded_of_precedenceMultisetMeasure /
-- _LexMeasure are the RPO certificates for multiset-status / lex-status symbols: a step terminates if the
-- precedence rank decreases or stays equal while the argument measure decreases.  Zero-axiom: Or-inversion +
-- InvImage.wf.
#assert_no_axioms FX1Poly.Core.LexPair

#assert_no_axioms FX1Poly.Core.LexPair.pairAccessible

#assert_no_axioms FX1Poly.Core.LexPair.isWellFounded

#assert_no_axioms FX1Poly.Core.wellFounded_of_lexPairMeasure

#assert_no_axioms FX1Poly.Core.wellFounded_of_precedenceMultisetMeasure

#assert_no_axioms FX1Poly.Core.wellFounded_of_precedenceLexMeasure

end FX1PolyAudit
