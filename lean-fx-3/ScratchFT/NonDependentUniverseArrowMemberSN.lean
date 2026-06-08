import FX1Poly.Typed.DenoteKeyedUniverseDomainPiMemberSN
import FX1Poly.Typed.DenoteKeyedNonDependentArrow
import FX1Poly.Core.StratifiedReducibleTypeCandidate

/-! Scratch probe: member-SN companion to the shipped type-level non-dependent universe-domain arrow
    (`universeDomainNonDependentArrow`) — completing the unconditional slice of #752 at the member level. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- Member-SN for the non-dependent universe-domain arrow `Type@e → codomainBase`: a reducible member is SN,
given the base codomain reducible-at-level with a reducibility-candidate. The constant codomain candidate makes
SN-D7's per-argument codomain obligation collapse (weaken-cancellation), so no domain drift / piArm is needed. -/
theorem universeDomainNonDependentArrowMemberStronglyNormalizing {scope : Nat} (env : Nat → Nat) (level : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    {codomainBase : RawTerm scope} {codomainBaseCandidate : RawTerm scope → Prop}
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (codomainCandidateHood : IsReducibilityCandidate codomainBaseCandidate)
    (codomainReducible : ReducibleTypeAtDenote env level codomainBase codomainBaseCandidate)
    {functionTerm : RawTerm scope}
    (member : IsReducibleMemberAtDenote env level
      (piTyCodeCell (universeCodeCell levelExpr flag) (RawTerm.weaken codomainBase)) functionTerm) :
    IsStronglyNormalizing functionTerm := by
  refine universeDomainPiMemberStronglyNormalizing env level levelExpr flag
    (codomainCandidate := fun _argument => codomainBaseCandidate) levelAbove
    (fun _argument _argumentInDomain => codomainCandidateHood)
    (fun argument _argumentInDomain => ?_) member
  rw [show RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase from
    RawTerm.weaken_subst_singleton codomainBase argument]
  exact codomainReducible

/-- **Fully-unconditional concrete witness:** a reducible member of `Type@e → Type@e'` (a function between two
universes) is strongly normalizing, at any level above both decoded levels — no hypotheses on the codomain (the
universe code is reducible-at-level directly and its candidate is a reducibility candidate via the bounded legs).
The first unconditional universe-domain function-type member-SN in the denote model. -/
theorem universeToUniverseArrowMemberStronglyNormalizing {scope : Nat} (env : Nat → Nat) (level : Nat)
    (domainLevel codomainLevel : LevelExpr) (domainFlag codomainFlag : UniverseFlag)
    (domainAbove : LevelExpr.denote domainLevel env < level)
    (codomainAbove : LevelExpr.denote codomainLevel env < level)
    {functionTerm : RawTerm scope}
    (member : IsReducibleMemberAtDenote env level
      (piTyCodeCell (universeCodeCell domainLevel domainFlag)
        (RawTerm.weaken (universeCodeCell codomainLevel codomainFlag))) functionTerm) :
    IsStronglyNormalizing functionTerm := by
  refine universeDomainNonDependentArrowMemberStronglyNormalizing env level domainLevel domainFlag
    (codomainBase := universeCodeCell codomainLevel codomainFlag)
    (codomainBaseCandidate := universeDenotePredicate env (denoteBelowFamily env level) codomainLevel)
    domainAbove ?_ ?_ member
  · exact ReducibleTypeStep.universeCandidateIsReducibilityCandidate
      (scope := scope)
      (lowerReducible := denoteBelowFamily env level (LevelExpr.denote codomainLevel env))
      (fun reducibleMember step =>
        denoteBelowFamily_forwardStep env level (LevelExpr.denote codomainLevel env) reducibleMember step)
      (fun neutral reductsReducible =>
        denoteBelowFamily_neutralInclusion_of_lt env level (LevelExpr.denote codomainLevel env) codomainAbove
          neutral reductsReducible)
  · exact ReducibleTypeStepDenote.universeCode codomainLevel codomainFlag

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeDomainNonDependentArrowMemberStronglyNormalizing
#print axioms FX1Poly.Typed.universeToUniverseArrowMemberStronglyNormalizing
