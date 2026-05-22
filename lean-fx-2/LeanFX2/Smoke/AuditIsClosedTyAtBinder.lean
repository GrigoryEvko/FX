import LeanFX2.Foundation.IsClosedTyAtBinder

/-! Smoke audit: `Foundation/IsClosedTyAtBinder.lean` zero-axiom log.

Reviewer-facing `#print axioms` confirms every shipped declaration in
the IsClosedTyAtBinder foundation does not depend on any axiom —
propext, Quot.sound, Classical.choice, or any user-declared axiom.

Verifies the meta-unblocker for the Σ-dependent-codomain leaf arms
(`unblock-A.leaf.pair` #2010 + sibling binder-Ty leaves).  Per the
design discussion in `Foundation/IsClosedTyAtBinder.lean:1-60`, the
predicate is shipped as an existential wrapper over the existing
`Ty.weaken` reducible alias — paralleling the
`IsClosedRawTerm` architectural choice (commit 57f92b28 +
623216ab) at the typed Ty layer rather than at the RawTerm layer. -/

namespace LeanFX2.SmokeIsClosedTyAtBinder

#print axioms LeanFX2.IsClosedTyAtBinder
#print axioms LeanFX2.IsClosedTyAtBinder.of_weaken_eq
#print axioms LeanFX2.IsClosedTyAtBinder.weaken_self
#print axioms LeanFX2.IsClosedTyAtBinder.imp_weaken
#print axioms LeanFX2.IsClosedTyAtBinder.subst0_invariant
#print axioms LeanFX2.IsClosedTyAtBinder.subst0_eq_inner

end LeanFX2.SmokeIsClosedTyAtBinder
