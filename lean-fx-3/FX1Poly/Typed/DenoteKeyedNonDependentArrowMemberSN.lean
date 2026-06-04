import FX1Poly.Typed.DenoteKeyedUniverseDomainPiMemberSN
import FX1Poly.Typed.DenoteKeyedNonDependentArrow
import FX1Poly.Core.StratifiedReducibleTypeCandidate

/-! # FX1Poly/Typed/DenoteKeyedNonDependentArrowMemberSN
    — member-SN for the non-dependent universe-domain arrow (the member half of the unconditional slice of #752)

`DenoteKeyedNonDependentArrow.lean` ships the TYPE-level result `universeDomainNonDependentArrow`: the
non-dependent arrow `Type@e → codomainBase` is reducible-as-a-type at every denote level whenever the base
codomain is — the unconditional slice of the #752 composite-domain `piArm` (the codomain crosses the binder as a
pure weakening, so the weaken-cancellation `RawTerm.weaken_subst_singleton` collapses the per-argument codomain
obligation to a constant, and the domain candidate's per-level drift — the obstruction — is never consumed).

This file adds the MEMBER half: a reducible member of that non-dependent universe-domain arrow is strongly
normalizing.  Together they complete the unconditional slice of #752 at BOTH the type and member levels — only
the genuinely DEPENDENT composite-domain Π stays gated on the deep obstruction.

## Why this is unblocked

It is the non-dependent specialization of SN-D7 (`universeDomainPiMemberStronglyNormalizing`,
`DenoteKeyedUniverseDomainPiMemberSN.lean`).  SN-D7 needs the codomain candidate to be a reducibility candidate
under each domain member and the codomain code reducible-at-level under each domain member; for a non-dependent
arrow both become CONSTANT (the codomain candidate ignores the argument), and the weaken-cancellation discharges
the codomain-reducibility obligation from the single base-codomain fact.  No cumulativity transport, no domain
drift, no piArm — the same crack past the level-drift wall the type-level slice uses, now at the member level.

## What lands here (both zero-axiom)

  * `universeDomainNonDependentArrowMemberStronglyNormalizing` — the general member-companion: given the base
    codomain reducible-at-level with a reducibility candidate, a reducible member of `Type@e → codomainBase` is
    SN.  The member half of `universeDomainNonDependentArrow`.
  * `universeToUniverseArrowMemberStronglyNormalizing` — the fully-unconditional concrete witness: a reducible
    member of `Type@e → Type@e'` (a function between two universes) is SN at any level above both decoded levels,
    with NO codomain hypotheses (the universe code is reducible-at-level directly via `.universeCode`, and its
    candidate is a reducibility candidate via the bounded `denoteBelowFamily` legs).  The first unconditional
    universe-domain function-type member-SN in the denote model.

## Zero-axiom verification

`universeDomainNonDependentArrowMemberStronglyNormalizing` applies SN-D7 with a constant codomain candidate and
discharges the per-argument obligation by `RawTerm.weaken_subst_singleton`.  The concrete witness instantiates
the base codomain to a universe code and discharges the two codomain hypotheses through
`ReducibleTypeStep.universeCandidateIsReducibilityCandidate` (bounded legs) and `ReducibleTypeStepDenote.
universeCode`.  No induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Member-SN for the non-dependent universe-domain arrow `Type@e → codomainBase`.**  Given the base codomain
reducible-at-level with a reducibility candidate, every reducible member of `Type@e → codomainBase` is strongly
normalizing.  The member companion to the shipped type-level `universeDomainNonDependentArrow`: SN-D7
(`universeDomainPiMemberStronglyNormalizing`) with a CONSTANT codomain candidate, whose per-argument codomain
obligation collapses by the weaken-cancellation `RawTerm.weaken_subst_singleton` — so the domain candidate's
per-level drift (the #752 obstruction) is never consumed.  Completes the unconditional slice of #752 at the
member level. -/
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

/-- **Fully-unconditional concrete witness: a reducible member of `Type@e → Type@e'` is strongly normalizing.**
A function between two universes (at any level above both decoded levels) — its members are SN with NO codomain
hypotheses: the codomain universe code is reducible-at-level directly via `ReducibleTypeStepDenote.universeCode`,
and its candidate is a reducibility candidate via the bounded `denoteBelowFamily` legs (the `< level` bound holds
by `codomainAbove`).  The first unconditional universe-domain function-type member-SN in the denote model — the
concrete payoff of the unconditional #752 slice. -/
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
