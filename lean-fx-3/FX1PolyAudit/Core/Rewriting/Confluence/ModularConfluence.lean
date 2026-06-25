import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Confluence.ModularConfluence

/-! # FX1PolyAudit.Core.Rewriting.Confluence.ModularConfluence

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Confluence.ModularConfluence`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The textbook CLOSURE-form Hindley-Rosen / Toyama confluence engine (ModularConfluence.lean): each side
-- CONFLUENT + reflexive-transitive closures strongly commute ⟹ union confluent, lifting
-- confluentOfUnionDiamonds across (R ∪ S)* = (R* ∪ S*)* (monotone forward / collapse back, no propext —
-- Confluent rel IS DiamondProperty (ReflTransClosure rel)).  completeReduction is the non-vacuity witness
-- (the criterion fires on the complete relation, with real steps).  Confluence is modular; SN is NOT
-- (Toyama's counterexample) — see accUnion's explicit quasi-commutation hypothesis.
#assert_no_axioms FX1Poly.Core.confluentOfCommutingConfluent

#assert_no_axioms FX1Poly.Core.completeReduction

#assert_no_axioms FX1Poly.Core.completeReduction_isConfluent

#assert_no_axioms FX1Poly.Core.completeReduction_closuresCommute

#assert_no_axioms FX1Poly.Core.completeModularConfluence

end FX1PolyAudit
