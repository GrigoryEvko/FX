import FX1Poly.Typed.ReducibleTypeAtAllLevelsPiDomainMemberExtension

/-! # FX1Poly/Typed/ReducibleMemberAtAllPositiveLevelsPiMemberExtension
    — the MEMBER leg of the Π `piType` arm: function member-extension from domain+codomain member-extension

`ReducibleTypeAtAllLevelsPiDomainMemberExtension` gave the TYPE leg of the Π `piType` arm (a Π type is
all-levels reducible given domain member-extension).  This file gives the MEMBER leg: a member of a Π type
at a positive level extends to all positive levels, given that the domain and codomain admit member-
extension.  Together the two legs reduce the entire `piType` arm of mutual type+member level-irrelevance to
domain+codomain member-extension — exactly what the mutual induction supplies from its inductive hypothesis
on the (structurally smaller) domain and codomain.

The construction is the application chain, run entirely at POSITIVE levels (so the degenerate fuel-`0` base
is never touched): at each target positive level `posLevel + 1`, rebuild the Π membership with the domain's
canonical member-predicate and the codomain's canonical member-predicate; for a fresh argument at
`posLevel + 1`, strengthen it by domain member-extension to a member at the source level `predLevel + 1`,
apply `IsReducibleMemberAt.application` (the function at `predLevel + 1` to the argument at `predLevel + 1`),
then strengthen the resulting codomain member by codomain member-extension back up to `posLevel + 1`.

The source membership is required at a POSITIVE level (`predLevel + 1`): from a fuel-`0` Π membership the
argument could only be strengthened to positive levels, leaving the `application` mismatched — this is the
degenerate-base obstruction, confined here to the fuel-`0` source case (and, in the mutual induction, to the
universe `piType`/member arm).

## Zero-axiom verification

The `piType` constructor with canonical member-candidates (`reducibleMemberCandidate`) plus the application
chain; no induction.  Verified `#print axioms` clean: no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Member leg of the Π `piType` arm.**  A positive-level member of a Π type extends to all positive
levels, given the domain is reducible at all levels and both the domain and codomain admit member-extension.
The dual of `IsReducibleTypeAtAllLevels.piTypeOfDomainMemberExtension`; together they discharge the `piType`
arm of mutual type+member level-irrelevance from domain+codomain member-extension. -/
theorem IsReducibleMemberAtAllPositiveLevels.piTypeMemberExtension {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {functionTerm : RawTerm scope} {predLevel : Nat}
    (domainAllLevels : IsReducibleTypeAtAllLevels domainCode)
    (domainMemberExtension : ∀ argument : RawTerm scope, ∀ {memberLevel : Nat},
        IsReducibleMemberAt memberLevel domainCode argument →
          IsReducibleMemberAtAllPositiveLevels domainCode argument)
    (codomainAllLevels : ∀ argument : RawTerm scope,
        IsReducibleMemberAtAllPositiveLevels domainCode argument →
          IsReducibleTypeAtAllLevels (RawTerm.subst0 codomainCode argument))
    (codomainMemberExtension : ∀ argument : RawTerm scope,
        IsReducibleMemberAtAllPositiveLevels domainCode argument →
          ∀ applicationTerm : RawTerm scope, ∀ {memberLevel : Nat},
            IsReducibleMemberAt memberLevel (RawTerm.subst0 codomainCode argument) applicationTerm →
              IsReducibleMemberAtAllPositiveLevels (RawTerm.subst0 codomainCode argument) applicationTerm)
    (member : IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      functionTerm) :
    IsReducibleMemberAtAllPositiveLevels
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      functionTerm := by
  intro posLevel
  refine ⟨fun ft => ∀ argument : RawTerm scope, IsReducibleMemberAt (posLevel + 1) domainCode argument →
      IsReducibleMemberAt (posLevel + 1) (RawTerm.subst0 codomainCode argument)
        (.mkGen .gen_app () (.childCons ft (.childCons argument .childNil))),
    ReducibleTypeStep.piType
      (fun argument => IsReducibleMemberAt (posLevel + 1) (RawTerm.subst0 codomainCode argument))
      (domainAllLevels (posLevel + 1)).reducibleMemberCandidate
      (fun argument argumentInDomain =>
        ((codomainAllLevels argument (domainMemberExtension argument argumentInDomain))
          (posLevel + 1)).reducibleMemberCandidate),
    ?_⟩
  intro argument argumentAtPosLevel
  have argumentAllPositive := domainMemberExtension argument argumentAtPosLevel
  have applicationAtPredLevel :=
    IsReducibleMemberAt.application member (argumentAllPositive predLevel)
  exact codomainMemberExtension argument argumentAllPositive _ applicationAtPredLevel posLevel

end FX1Poly.Typed
