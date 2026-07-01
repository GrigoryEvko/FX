import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.Orders.TerminationOrders

/-! # FX1PolyAudit.Polygraph.Rewriting.Orders.TerminationOrders

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.Rewriting.Orders.TerminationOrders`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The lexicographic list order + well-foundedness (the lex companion to the multiset order, the comparison
-- LPO uses for arguments and RPO for lex-status symbols) + measure-based termination certificates over both
-- orders.  LexListStep is the existential-on-List lex single step (length-matched tails); isWellFounded via
-- length-indexed nested accessibility.  wellFounded_of_multisetMeasure/_lexMeasure turn a measure-decrease
-- into WellFounded via InvImage.wf.  Zero-axiom: List-existential inversion (cases commonPrefix), defeq length
-- + local length_append, Nat.noConfusion directly (absurd + succ_ne_zero leaks propext).
#assert_no_axioms FX1Poly.Core.LexListStep

#assert_no_axioms FX1Poly.Core.LexListStep.length_eq

#assert_no_axioms FX1Poly.Core.LexListStep.emptyAccessible

#assert_no_axioms FX1Poly.Core.LexListStep.consAccessible

#assert_no_axioms FX1Poly.Core.LexListStep.accessibleByLength

#assert_no_axioms FX1Poly.Core.LexListStep.isWellFounded

#assert_no_axioms FX1Poly.Core.wellFounded_of_multisetMeasure

#assert_no_axioms FX1Poly.Core.wellFounded_of_lexMeasure

end FX1PolyAudit
