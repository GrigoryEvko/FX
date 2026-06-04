import FX1Poly.Typed.DenoteKeyedPiFormationFromExistence

/-! # FX1Poly/Typed/DenoteKeyedGeneralDomainPiArm
    — the GENERAL domain piArm modulo domain member-stability (the precise A2 residual; toward SN-043/#752)

The backbone `IsReducibleTypeAtAllDenoteLevels.ofReducibleTypeStepDenote` (`DenoteKeyedLevelIrrelevance.lean`)
leaves the `piType` arm — the all-level reducibility of `Π domainCode codomainCode` — as the supplied `piArm`
hypothesis (#752 / the denote A2 residual).  The shipped from-existence instances
(`DenoteKeyedPiFormationFromExistence.lean`) discharge it for three domain shapes:
  * UNIFORM-candidate domains (`uniformDomainPi_reducibleFromCodomainExistence`),
  * NEUTRAL domains (`neutralDomainPi_…`, the witnessing instance), and
  * UNIVERSE domains (`universeDomainPi_…`, threshold-split).
Each supplies a SINGLE domain candidate as DATA.  But the backbone's domain induction hypothesis is
`IsReducibleTypeAtAllDenoteLevels env domainCode` = `∀ level, ∃ candidate, ReducibleTypeAtDenote env level
domainCode candidate` — a candidate PER LEVEL, which may DIFFER (drift) per level.  Collapsing the per-level
candidates into the single candidate the `piType` assembly needs is EXACTLY domain MEMBER-STABILITY: a
denote-reducible member of the domain at one level is a member at every level.

This file isolates that residual.  `generalDomainPi_reducibleFromMemberStability` takes the domain's per-level
reducibility (the backbone's domain IH, drift allowed) PLUS domain member-stability and produces the Π at every
level — strictly MORE GENERAL than the uniform piArm, which is its member-stable-by-a-uniform-candidate
instance (member-stability from a single candidate via `ReducibleTypeAtDenote.deterministic`; verified in
scratch as `uniformDomainPi_viaMemberStability`).  It covers member-stable COMPOSITE domains — `Nat → Nat`,
neutral-component formers — that the uniform/neutral instances cannot reach without a uniform candidate supplied
as data.  The remaining residual is now precisely the THRESHOLD-DRIFT domains: composite domains CONTAINING
sub-threshold universe codes, whose members genuinely fail member-stability below the threshold (e.g.
`Type@0 → Type@0`).  Those need the threshold-split argument (the universe-domain piArm's technique generalized);
the member-stable composite domains close here.

## The construction

At each `level`, fire `piType` with the canonical member-predicate as both domain and codomain candidate
(`reducibleMemberCandidate` on the per-level domain reducibility / on the codomain existence), discharging the
codomain obligation from existence — no `Classical.choice`.  The domain membership `argumentInDomain` (canonical
at `level`) is lifted to membership at EVERY level by `domainMemberStable`, which is exactly the codomain
existence's gate.

## Zero-axiom verification

A single anonymous-constructor term: `fun level => ⟨_, ReducibleTypeStepDenote.piType … …⟩`, the domain premise
`(domainAllLevel level).reducibleMemberCandidate`, the codomain premise
`(codomainExistence … level).reducibleMemberCandidate`, the gate bridged by `domainMemberStable`.  No tactic, no
recursion.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The general domain piArm modulo domain member-stability.**  Given the domain reducible at every denote
level (the backbone's domain IH — its per-level candidate is allowed to drift) and domain MEMBER-STABILITY (a
denote-reducible member of the domain at one level is a member at every level), plus the codomain reducible at
all levels for every argument that is a domain member at every level, `Π domainCode codomainCode` is reducible
at every denote level.  At each level the canonical member-predicate is the domain/codomain candidate
(`reducibleMemberCandidate`), and member-stability lifts the per-level domain membership to the all-level
membership the codomain existence is gated by.  Strictly generalizes the uniform-candidate piArm (its
member-stable-by-a-uniform-candidate instance); reaches member-stable COMPOSITE domains.  The residual the
backbone still needs is exactly this domain member-stability, which for threshold-drift domains (containing
sub-threshold universe codes) fails below threshold and needs the threshold-split. -/
theorem generalDomainPi_reducibleFromMemberStability {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainAllLevel : IsReducibleTypeAtAllDenoteLevels env domainCode)
    (domainMemberStable : ∀ (sourceLevel targetLevel : Nat) (argument : RawTerm scope),
      IsReducibleMemberAtDenote env sourceLevel domainCode argument →
      IsReducibleMemberAtDenote env targetLevel domainCode argument)
    (codomainExistence : ∀ argument : RawTerm scope,
      (∀ memberLevel : Nat, IsReducibleMemberAtDenote env memberLevel domainCode argument) →
      IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  fun level => ⟨_, ReducibleTypeStepDenote.piType
    (fun argument => IsReducibleMemberAtDenote env level (RawTerm.subst0 codomainCode argument))
    ((domainAllLevel level).reducibleMemberCandidate)
    (fun argument argumentInDomain =>
      (codomainExistence argument
        (fun memberLevel => domainMemberStable level memberLevel argument argumentInDomain)
        level).reducibleMemberCandidate)⟩

end FX1Poly.Typed
