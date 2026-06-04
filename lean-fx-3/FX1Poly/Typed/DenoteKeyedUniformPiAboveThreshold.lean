import FX1Poly.Typed.DenoteKeyedUniformPiCandidate

/-! # FX1Poly/Typed/DenoteKeyedUniformPiAboveThreshold
    — above-threshold uniform-composite member-stability: the threshold-drift composite handler (#752)

`DenoteKeyedUniformPiCandidate.lean` lifted uniform candidacy / member-stability up the Π-former spine for
components uniform at ALL levels — composites with NO universe codes (`Nat → Nat`).  This file ships the
ABOVE-THRESHOLD analogues, the genuine handler for the remaining #752 residual: THRESHOLD-DRIFT composites that
CONTAIN universe codes (`Type@0 → Type@0`).  Their components are NOT uniform across all levels — the inner
universe code `Type@e` is the empty candidate at/below its decoded level `denote e env` and the level-irrelevant
decode set strictly above it (`universeMembership_levelIrrelevant`).  But ABOVE that threshold the candidate is
FIXED, so the whole composite is uniform there, and member-stability holds — bounded to levels above the
threshold.

Crucially the all-level reducibility these composites would need to fit the unbounded backbone is genuinely
unachievable (a Π over such a domain fails below the threshold), but the fundamental theorem never needs it: a
former's components live in universes strictly below the former's own, so the former's decoded level — the
single level at which the genFormationPi arm needs the former reducible — sits ABOVE every component threshold,
exactly the regime these lemmas cover.  Instantiating `domainReducible` for a universe-code component is the
shipped `universeMembership_levelIrrelevant` (its candidate is fixed above `denote e env`).

## The three declarations (above-threshold twins of `DenoteKeyedUniformPiCandidate`)

  * `uniformType_memberStableAboveThreshold` — a type with one fixed candidate at every level ABOVE the
    threshold is member-stable between any two above-threshold levels (`deterministic` between the source-level
    candidate and the fixed one, both invoked above threshold).
  * `uniformDomainPi_hasUniformCandidateAboveThreshold` — a Π whose domain and codomain are reducible with fixed
    candidates above the threshold is reducible with the fixed `piType` candidate at every above-threshold level
    (one `piType` per level, the candidate level-independent there).
  * `uniformDomainPi_memberStableAboveThreshold` — consequently such a Π is member-stable across above-threshold
    levels.

## Zero-axiom verification

`uniformType_memberStableAboveThreshold` is `deterministic` + reassembly (the above-threshold bound threaded
into the candidate invocations); `uniformDomainPi_hasUniformCandidateAboveThreshold` is one `piType` per
above-threshold level; the composite is their composition.  No tactic beyond `obtain`, no recursion, no
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Above-threshold member-stability for a uniform-candidate type.**  If `typeCode` is reducible with one fixed
`candidate` at every denote level strictly above `threshold`, then a denote-reducible member at one
above-threshold level is a member at every above-threshold level — the bounded analogue of
`uniformType_memberStableAcrossDenoteLevels`, for types uniform only above their universe codes' decoded
level. -/
theorem uniformType_memberStableAboveThreshold {scope : Nat} (env : Nat → Nat) (threshold : Nat)
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (uniformReducible : ∀ level : Nat, threshold < level →
      ReducibleTypeAtDenote env level typeCode candidate)
    {term : RawTerm scope} {sourceLevel : Nat} (sourceAbove : threshold < sourceLevel)
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel typeCode term)
    (targetLevel : Nat) (targetAbove : threshold < targetLevel) :
    IsReducibleMemberAtDenote env targetLevel typeCode term := by
  obtain ⟨sourceCandidate, sourceReducible, memberInSource⟩ := memberAtSource
  have candidatesAgree :=
    ReducibleTypeAtDenote.deterministic sourceReducible (uniformReducible sourceLevel sourceAbove)
  exact ⟨candidate, uniformReducible targetLevel targetAbove, (candidatesAgree term).mp memberInSource⟩

/-- **A Π over above-threshold-uniform components has a fixed candidate above the threshold.**  Given a domain
reducible with one candidate and a codomain reducible with one candidate function (per domain member) at every
level strictly above `threshold`, `Π domainCode codomainCode` is reducible at every above-threshold level with
the FIXED `piType` candidate — level-independent there because its components are.  The above-threshold twin of
`uniformDomainPi_hasUniformCandidate`, the lift for threshold-drift composites whose universe-code components
become uniform above their decoded level. -/
theorem uniformDomainPi_hasUniformCandidateAboveThreshold {scope : Nat} (env : Nat → Nat) (threshold : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, threshold < level →
      ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat), threshold < level → ∀ (argument : RawTerm scope),
      domainCandidate argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument)) :
    ∀ level : Nat, threshold < level → ReducibleTypeAtDenote env level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
        codomainCandidate argument
          (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) :=
  fun level levelAbove => ReducibleTypeStepDenote.piType codomainCandidate
    (domainReducible level levelAbove)
    (fun argument argumentInDomain => codomainReducible level levelAbove argument argumentInDomain)

/-- **A Π over above-threshold-uniform components is member-stable above the threshold.**  Since such a Π denotes
one fixed candidate above the threshold (`uniformDomainPi_hasUniformCandidateAboveThreshold`), its
denote-reducible members are stable across above-threshold levels — the composite member-stability the general
piArm needs for threshold-drift composite domains (`Type@0 → Type@0`), where it holds only above the inner
universe codes' decoded level. -/
theorem uniformDomainPi_memberStableAboveThreshold {scope : Nat} (env : Nat → Nat) (threshold : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, threshold < level →
      ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat), threshold < level → ∀ (argument : RawTerm scope),
      domainCandidate argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument))
    {term : RawTerm scope} {sourceLevel : Nat} (sourceAbove : threshold < sourceLevel)
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term)
    (targetLevel : Nat) (targetAbove : threshold < targetLevel) :
    IsReducibleMemberAtDenote env targetLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term :=
  uniformType_memberStableAboveThreshold env threshold
    (uniformDomainPi_hasUniformCandidateAboveThreshold env threshold domainCandidate domainReducible
      codomainCandidate codomainReducible)
    sourceAbove memberAtSource targetLevel targetAbove

end FX1Poly.Typed
