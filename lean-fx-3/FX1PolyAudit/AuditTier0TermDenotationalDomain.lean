import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Semantics.DenotationalDomain

/-! # FX1PolyAudit/AuditTier0TermDenotationalDomain — zero-axiom gate for term-21 (domain fixpoint)

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Term/Semantics/DenotationalDomain.lean`: the pointed
ω-CPO interface (`PointedDcpo` / `IsChain` / `Monotone` / `Continuous`), the iteration chain
(`iterate` / `iterate_isChain` / `sup_tail`), the Kleene least fixpoint (`kleeneFixpoint` /
`kleeneFixpoint_isFixpoint` / `kleeneFixpoint_isLeast`), and the one-point domain witness
(`trivialDomain` / `trivialDomain_kleeneFixpoint_eq`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The pointed ω-CPO interface
#assert_no_axioms FX1Poly.Core.PointedDcpo
#assert_no_axioms FX1Poly.Core.PointedDcpo.IsChain
#assert_no_axioms FX1Poly.Core.PointedDcpo.Monotone
#assert_no_axioms FX1Poly.Core.PointedDcpo.Continuous

-- The iteration chain + its sup
#assert_no_axioms FX1Poly.Core.PointedDcpo.iterate
#assert_no_axioms FX1Poly.Core.PointedDcpo.iterate_isChain
#assert_no_axioms FX1Poly.Core.PointedDcpo.sup_tail

-- The Kleene least fixpoint (recursion = least fixpoint)
#assert_no_axioms FX1Poly.Core.PointedDcpo.kleeneFixpoint
#assert_no_axioms FX1Poly.Core.PointedDcpo.kleeneFixpoint_isFixpoint
#assert_no_axioms FX1Poly.Core.PointedDcpo.kleeneFixpoint_isLeast

-- The one-point domain witness
#assert_no_axioms FX1Poly.Core.trivialDomain
#assert_no_axioms FX1Poly.Core.trivialDomain_kleeneFixpoint_eq

end FX1PolyAudit
