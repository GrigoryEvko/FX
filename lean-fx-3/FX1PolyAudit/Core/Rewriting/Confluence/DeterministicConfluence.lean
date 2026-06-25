import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Confluence.DeterministicConfluence

/-! # FX1PolyAudit.Core.Rewriting.Confluence.DeterministicConfluence

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Confluence.DeterministicConfluence`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Deterministic confluence (abstract toolkit, fourth route): a deterministic (functional) relation is
-- confluent, since its reflexive-transitive reducts from a common source are linearly ordered.  Determinism
-- does not give the strict diamond (a normal form breaks it), so this is its own linear-chain induction.  The
-- route for deterministic reduction strategies (weak-head here, the deterministic NbE evaluator downstream).
-- IsDeterministic + confluentOfDeterministic + the concrete WeakHeadStep.hasConfluence (weak-head reduction is
-- Church-Rosser, from WeakHeadStep.deterministic).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.IsDeterministic

#assert_no_axioms FX1Poly.Core.confluentOfDeterministicAux

#assert_no_axioms FX1Poly.Core.confluentOfDeterministic

#assert_no_axioms FX1Poly.Core.WeakHeadStep.hasConfluence

end FX1PolyAudit
