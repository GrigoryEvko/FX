import FX1Poly.Typed.DenoteKeyedLevelIrrelevance

/-! # FX1Poly/Typed/DenoteKeyedUniformPiCandidate
    — a Π former over uniform-candidate components has a SINGLE uniform candidate (composite member-stability;
      toward SN-043/#752)

The A2 residual after `DenoteKeyedGeneralDomainPiArm.generalDomainPi_reducibleFromMemberStability` is the
THRESHOLD-DRIFT domains: the general piArm needs domain MEMBER-STABILITY, and the shipped member-stability
lemmas (`DenoteKeyedLevelIrrelevance.{uniformType, neutralType}_memberStableAcrossDenoteLevels`) cover only LEAF
types (a single uniform candidate / a neutral type).  This file lifts member-stability to COMPOSITE Π formers
whose components are uniform — the recursive step that the leaf lemmas lacked.

The decisive observation: the `piType` candidate `fun functionTerm => ∀ argument, domainCandidate argument →
codomainCandidate argument (functionTerm argument)` does NOT depend on the ambient level when the domain and
codomain candidates do not.  So a Π over a uniform-candidate domain with a uniform-candidate codomain function
denotes ONE level-independent candidate at EVERY denote level — it is itself a uniform-candidate type.  Uniform
candidacy then composes up the Π/Σ-former spine, and `uniformType_memberStableAcrossDenoteLevels` delivers the
composite's member-stability for free.

This is exactly what lets the shipped uniform piArm (`uniformDomainPi_reducibleFromCodomainExistence`) and the
general piArm (`generalDomainPi_reducibleFromMemberStability`) reach composite domains like `Nat → Nat` or
`(Nat → Nat) → Bool`: supply the composite domain's uniform candidate from `uniformDomainPi_hasUniformCandidate`,
or its member-stability from `uniformDomainPi_memberStable`.  The remaining residual is precisely the
THRESHOLD-DRIFT domains — composite domains CONTAINING sub-threshold universe codes — whose candidate genuinely
varies with the level (the inner universe code is empty below its decoded level), so they are NOT uniform and
need the threshold-split, not this uniform-composition lemma.

## The two declarations

  * `uniformDomainPi_hasUniformCandidate` — a Π over a uniform-candidate domain with a uniform-candidate codomain
    function is reducible at EVERY denote level with the SAME `piType` candidate (the candidate is independent of
    `level` because its components are).  One `piType` per level, the candidate fixed.
  * `uniformDomainPi_memberStable` — consequently a Π over uniform components is member-stable across denote
    levels (`uniformType_memberStableAcrossDenoteLevels` applied to the uniform candidate).

## Zero-axiom verification

`uniformDomainPi_hasUniformCandidate` is `fun level => ReducibleTypeStepDenote.piType …` — one constructor per
level, the candidate stated explicitly (so it is visibly the same at every level).  `uniformDomainPi_memberStable`
is `uniformType_memberStableAcrossDenoteLevels` applied to it.  No tactic, no recursion, no `funext`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **A Π over uniform-candidate components has a SINGLE uniform candidate.**  Given a domain reducible with one
candidate at every denote level and a codomain reducible with one candidate function (per domain member) at every
level, `Π domainCode codomainCode` is reducible at EVERY denote level with the FIXED `piType` candidate
`fun functionTerm => ∀ argument, domainCandidate argument → codomainCandidate argument (functionTerm argument)`
— level-independent because its components are.  The recursive step lifting uniform candidacy from leaf types to
composite Π/Σ formers. -/
theorem uniformDomainPi_hasUniformCandidate {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat) (argument : RawTerm scope), domainCandidate argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument)) :
    ∀ level : Nat, ReducibleTypeAtDenote env level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
        codomainCandidate argument
          (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) :=
  fun level => ReducibleTypeStepDenote.piType codomainCandidate (domainReducible level)
    (fun argument argumentInDomain => codomainReducible level argument argumentInDomain)

/-- **A Π over uniform-candidate components is member-stable.**  Since the Π denotes one level-independent
candidate (`uniformDomainPi_hasUniformCandidate`), a denote-reducible member at one level is a member at every
level — the composite analogue of `uniformType_memberStableAcrossDenoteLevels`, the member-stability the general
piArm needs for composite (uniform-component) domains like `Nat → Nat`. -/
theorem uniformDomainPi_memberStable {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat) (argument : RawTerm scope), domainCandidate argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument))
    {term : RawTerm scope} {sourceLevel : Nat}
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term)
    (targetLevel : Nat) :
    IsReducibleMemberAtDenote env targetLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term :=
  uniformType_memberStableAcrossDenoteLevels env
    (uniformDomainPi_hasUniformCandidate env domainCandidate domainReducible
      codomainCandidate codomainReducible)
    memberAtSource targetLevel

end FX1Poly.Typed
