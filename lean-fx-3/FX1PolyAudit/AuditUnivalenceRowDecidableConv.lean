import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Univalence.UnivalenceRowDecidableConv

/-! # FX1PolyAudit/AuditUnivalenceRowDecidableConv — zero-axiom gate for the univalence-row decider

Per-declaration zero-axiom gate for `FX1Poly/Core/Substrate/Univalence/UnivalenceRowDecidableConv.lean`:
the closure lift of the preservation invariant (`reflTransClosure_preservesUnivNF`), the closure congruence
lifts (`reflTransClosure_cong`/`here`/`there`), the reach-its-normal-form theorems (`univNFRoot_reaches`,
`univNF_reaches`, `univNFChildren_reaches`), the decision iff (`joinable_iff_univNFEq`), the `Decidable`
instance (`instDecidableJoinableUnivalenceRowStep`), the non-vacuity witness, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega` — "decidable definitional univalence by computation", riding the deterministic
redex-free `univNF` and the zero-axiom `DecidableEq RawTerm`, no `Acc.rec` / SN / Newman / local-confluence
proof. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.reflTransClosure_preservesUnivNF
#assert_no_axioms FX1Poly.Core.reflTransClosure_cong
#assert_no_axioms FX1Poly.Core.reflTransClosure_here
#assert_no_axioms FX1Poly.Core.reflTransClosure_there
#assert_no_axioms FX1Poly.Core.univNFRoot_reaches
#assert_no_axioms FX1Poly.Core.univNF_reaches
#assert_no_axioms FX1Poly.Core.univNFChildren_reaches
#assert_no_axioms FX1Poly.Core.joinable_iff_univNFEq
#assert_no_axioms FX1Poly.Core.univalenceRowStep_confluent
#assert_no_axioms FX1Poly.Core.instDecidableJoinableUnivalenceRowStep
#assert_no_axioms FX1Poly.Core.univalenceRedex_joinable_reduct
#assert_no_axioms FX1Poly.Core.univalenceDecider_rejectsDistinctHeads
#assert_no_axioms FX1Poly.Core.fxUnivalenceConv_decidesByComputation
#assert_no_axioms FX1Poly.Core.fxUnivalenceConv_isGlobalKernelConv

end FX1PolyAudit
