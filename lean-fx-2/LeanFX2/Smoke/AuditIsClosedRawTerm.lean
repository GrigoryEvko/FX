import LeanFX2.Foundation.IsClosedRawTerm

/-! Smoke audit: `Foundation/IsClosedRawTerm.lean` zero-axiom log.

Reviewer-facing `#print axioms` confirms every shipped declaration in
the IsClosedRawTerm foundation does not depend on any axiom — propext,
Quot.sound, Classical.choice, or any user-declared axiom.

Verifies the meta-unblocker for the 20 `unblock-A.dispatch.*` and
`unblock-A.leaf.*` arms whose blocker is raw-payload preservation
under `Step.par`.  Per the design discussion in
`Foundation/IsClosedTy.lean:46-58`, the predicate is shipped as an
existential wrapper over the existing `RawTerm.unweaken?` recognizer
rather than a 78-ctor inductive — this trims the ~200 LoC estimate
down to ~30 LoC while keeping the predicate Prop-valued and
compatible with the planned `IsClosedTy.id`, `IsClosedTy.oeq`,
`IsClosedTy.idStrict`, `IsClosedTy.path`, `IsClosedTy.glue`,
`IsClosedTy.refine`, `IsClosedTy.session`, `IsClosedTy.effect`
extensions. -/

namespace LeanFX2.SmokeIsClosedRawTerm

#print axioms LeanFX2.IsClosedRawTerm
#print axioms LeanFX2.IsClosedRawTerm.of_unweaken_some
#print axioms LeanFX2.IsClosedRawTerm.imp_weaken
#print axioms LeanFX2.IsClosedRawTerm.of_weaken_eq
#print axioms LeanFX2.IsClosedRawTerm.weaken_self

end LeanFX2.SmokeIsClosedRawTerm
