import FX1Poly.Typed.ReducibleMemberAtAllPositiveLevelsLeaves

/-! # FX1Poly/Typed/ReducibleMemberAtAllPositiveLevelsHeadExpand
    — member-extension is preserved under weak-head expansion of the classifier

The member-side `whnfExpand` arm of mutual type+member level-irrelevance: if the weak-head contractum of a
classifier admits member-extension (one-level members strengthen to all-positive members), then so does the
classifier itself.  A member of the redex classifier peels to a member of the contractum at the same level
(`ReducibleTypeStep.candidateAtWhnfReduct` — the candidate is shared across the weak-head step), the
contractum's member-extension strengthens it to all-positive, and `IsReducibleMemberAtAllPositiveLevels.
headExpand` lifts the all-positive contractum member back across the weak-head step to the classifier.

With the member-side leaf (`ofNeutralClassifier`, the `neutral` arm) this completes the member-side arm
family for the non-`piType`/non-`universeCode` cases — the structurally-recursive part of member
level-irrelevance.

## Zero-axiom verification

`cases` on the level (to project `candidateAtWhnfReduct` off the `ReducibleTypeStep` layer), the member
peel, the contractum's member-extension, and the value-level head-expansion.  No induction.  Verified
`#print axioms` clean: no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Member-extension lifts backward across one weak-head step of the classifier.**  If the weak-head
contractum `reduct` of `classifier` admits member-extension, so does `classifier`: peel the member to the
contractum (shared candidate), strengthen by the contractum's member-extension, and head-expand the
resulting all-positive contractum member back to the classifier. -/
theorem IsReducibleMemberAtAllPositiveLevels.extensionHeadExpand {scope : Nat}
    {classifier reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep classifier reduct)
    (reductMemberExtension : ∀ {level : Nat} (term : RawTerm scope),
        IsReducibleMemberAt level reduct term → IsReducibleMemberAtAllPositiveLevels reduct term) :
    ∀ {level : Nat} (term : RawTerm scope),
      IsReducibleMemberAt level classifier term →
        IsReducibleMemberAtAllPositiveLevels classifier term := by
  intro level term member
  obtain ⟨candidate, reducible, candidateTerm⟩ := member
  cases level with
  | zero =>
      exact IsReducibleMemberAtAllPositiveLevels.headExpand weakHeadStep
        (reductMemberExtension (level := 0) term
          ⟨candidate, reducible.candidateAtWhnfReduct weakHeadStep, candidateTerm⟩)
  | succ predLevel =>
      exact IsReducibleMemberAtAllPositiveLevels.headExpand weakHeadStep
        (reductMemberExtension (level := predLevel + 1) term
          ⟨candidate, reducible.candidateAtWhnfReduct weakHeadStep, candidateTerm⟩)

end FX1Poly.Typed
