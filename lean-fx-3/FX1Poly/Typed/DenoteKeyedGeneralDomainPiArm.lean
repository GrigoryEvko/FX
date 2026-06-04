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

/-- **The uniform-candidate piArm ADAPTER — consuming the backbone's own existential-candidate codomain IH.**
The `ofReducibleTypeStepDenote` piArm (`DenoteKeyedLevelIrrelevance.lean`) supplies the codomain induction
hypothesis as `∀ argument, domainCandidate argument → IsReducibleTypeAtAllDenoteLevels env (subst0 codomainCode
argument)` — an EXISTENTIAL-candidate all-level reducibility keyed on the step's `domainCandidate`.  The shipped
`uniformDomainPi_reducibleAtEveryDenoteLevel` instead consumes a CONCRETE per-level codomain candidate, so it
cannot be plugged into the backbone piArm directly.  This adapter bridges the two for a UNIFORM domain candidate
(reducible at every level with one fixed `domainCandidate`): it routes through `generalDomainPi_reducibleFrom
MemberStability`, supplying member-stability from `uniformType_memberStableAcrossDenoteLevels`, and discharging
the member-stability lemma's all-level-member gate by reconciling its candidate with the codomain IH's
`domainCandidate` via `ReducibleTypeAtDenote.deterministic` at level 0.  Choice-free — the level-0 member's
candidate is pinned to `domainCandidate`, so the codomain IH fires with no `Classical`. -/
theorem uniformDomainPiArmFromInductiveHypotheses {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    (domainUniform : ∀ level : Nat, ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainInductiveHypothesis : ∀ argument : RawTerm scope, domainCandidate argument →
      IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  generalDomainPi_reducibleFromMemberStability env
    (fun level => ⟨domainCandidate, domainUniform level⟩)
    (fun _sourceLevel targetLevel _argument memberAtSource =>
      uniformType_memberStableAcrossDenoteLevels env domainUniform memberAtSource targetLevel)
    (fun argument memberAllLevels => by
      obtain ⟨sourceCandidate, sourceReducible, memberInSource⟩ := memberAllLevels 0
      exact codomainInductiveHypothesis argument
        ((ReducibleTypeAtDenote.deterministic sourceReducible (domainUniform 0) argument).mp
          memberInSource))

/-- **The neutral-domain piArm adapter (witnessing instance).**  A weak-head-normal non-Π non-universe DOMAIN
has the literally-uniform candidate `IsStronglyNormalizing` at every level (the `neutral` step references
neither the lower family nor the level), so `uniformDomainPiArmFromInductiveHypotheses` applies.  This is the
neutral arm of the `ofReducibleTypeStepDenote` piArm case-split, in exactly the shape the backbone supplies its
premises — the codomain IH is keyed on argument strong-normalization (= `domainCandidate` in the neutral case),
matching the backbone's `codomainInductiveHypothesis` definitionally.  The remaining arms of the case-split are
the universe-code domain (`DenoteKeyedUniverseDomainPi`) and the composite/threshold-drift domain (the open
#752 residual). -/
theorem neutralDomainPiArmFromInductiveHypotheses {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (notPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (codomainInductiveHypothesis : ∀ argument : RawTerm scope, IsStronglyNormalizing argument →
      IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  uniformDomainPiArmFromInductiveHypotheses env
    (fun _level => ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse)
    codomainInductiveHypothesis

end FX1Poly.Typed
