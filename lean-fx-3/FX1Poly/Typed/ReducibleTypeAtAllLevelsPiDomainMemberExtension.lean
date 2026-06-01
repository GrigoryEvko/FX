import FX1Poly.Typed.ReducibleTypeAtAllLevelsPiNeutralDomain

/-! # FX1Poly/Typed/ReducibleTypeAtAllLevelsPiDomainMemberExtension
    — the Π `piType` arm of level-irrelevance reduced to DOMAIN MEMBER-EXTENSION

`ReducibleTypeAtAllLevelsPiNeutralDomain` closed the `piType` arm of type-level level-irrelevance for a
NEUTRAL / data-former domain.  This file generalizes that to an ARBITRARY domain, isolating the precise
remaining type-side obstruction: the Π type is reducible at all levels as soon as its domain is reducible at
all levels, its domain admits MEMBER-EXTENSION (one-level domain members strengthen to all-positive domain
members), and its codomain is reducible at all levels for every all-positive domain member.

The domain-candidate level-mismatch that blocks the general `piType` arm is exactly dissolved by domain
member-extension: at each level the Π type is rebuilt with the domain's FIXED canonical member-predicate
(`IsReducibleMemberAt level domainCode`, from `reducibleMemberCandidate`), and a level-`m` domain member is
strengthened by member-extension to an all-positive member, which the codomain hypothesis turns into
codomain reducibility at `m` (canonical codomain candidate, choice-free).  For a neutral / data-former
domain, member-extension is the member-side leaf (`IsReducibleMemberAtAllPositiveLevels.ofNeutralClassifier`),
recovering `piTypeOfNeutralDomain`.

This is the TYPE leg of the mutual type+member level-irrelevance induction: the `piType` type arm needs only
domain member-extension, which the mutual induction supplies from its member-side inductive hypothesis on
the (structurally smaller) domain.  The residual obstruction is therefore purely member-side — member-
extension for Π- and universe-classifier domains — bottoming out at the universe member-extension (the open
type-polymorphic core).

## Zero-axiom verification

`cases` on the level, the `piType` constructor with the domain's canonical member-candidate and the
codomain's canonical member-candidate (via `IsReducibleTypeAt.reducibleMemberCandidate`), the codomain
reducibility fed by domain member-extension.  No induction.  Verified `#print axioms` clean: no `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Level-irrelevance for a Π type, reduced to domain member-extension.**  A Π type is reducible at all
levels when its domain is reducible at all levels, its domain admits member-extension (one-level domain
members extend to all-positive domain members), and its codomain is reducible at all levels for every
all-positive domain member.  Generalizes `piTypeOfNeutralDomain` from neutral domains (where member-
extension is the member-side leaf) to any domain; the precise type-side obstruction is now exactly domain
member-extension. -/
theorem IsReducibleTypeAtAllLevels.piTypeOfDomainMemberExtension {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainAllLevels : IsReducibleTypeAtAllLevels domainCode)
    (domainMemberExtension : ∀ (argument : RawTerm scope) {memberLevel : Nat},
        IsReducibleMemberAt memberLevel domainCode argument →
          IsReducibleMemberAtAllPositiveLevels domainCode argument)
    (codomainAllLevelsForAllPositiveArgument : ∀ argument : RawTerm scope,
        IsReducibleMemberAtAllPositiveLevels domainCode argument →
          IsReducibleTypeAtAllLevels (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllLevels
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) := by
  intro level
  cases level with
  | zero =>
      refine ⟨_, ReducibleTypeStep.piType
        (fun argument => IsReducibleMemberAt 0 (RawTerm.subst0 codomainCode argument))
        (domainAllLevels 0).reducibleMemberCandidate
        (fun argument argumentInDomain => ?_)⟩
      exact ((codomainAllLevelsForAllPositiveArgument argument
        (domainMemberExtension argument argumentInDomain)) 0).reducibleMemberCandidate
  | succ predLevel =>
      refine ⟨_, ReducibleTypeStep.piType
        (fun argument => IsReducibleMemberAt (predLevel + 1) (RawTerm.subst0 codomainCode argument))
        (domainAllLevels (predLevel + 1)).reducibleMemberCandidate
        (fun argument argumentInDomain => ?_)⟩
      exact ((codomainAllLevelsForAllPositiveArgument argument
        (domainMemberExtension argument argumentInDomain)) (predLevel + 1)).reducibleMemberCandidate

end FX1Poly.Typed
