import FX1Poly.Typed.DenoteKeyedBoundedGenFormationPiArm

/-! # FX1Poly/Typed/DenoteKeyedBoundedGenFormationPiDischarge
    — the bound-carrying `piReducibleAsType` DISCHARGE variants: THE PAYOFF (#753 → SN-043)

The bound-carrying analogues of `DenoteKeyedGenFormationPiArm`'s `piReducibleAsType` discharge variants —
the lemmas that supply the `piReducibleAsType` premise of `fundamentalGenFormationPiAtBounded` from the children's
reducibility.  This is where the entire bounded refactor pays off.

## The model-obstructed case the bounded relation uniquely closes

The denote relation can discharge the `piReducibleAsType` premise of `Π domain. codomain : Type@levelExpr` ONLY
when each child is classified at the SAME universe as the Π's output (`piReducibleAsTypeFromUniformLevelMember`), or
when a child is a literal universe CODE (anti-vacuity).  The remaining shape — a child that is a universe MEMBER
classified at a level STRICTLY BELOW `levelExpr` (so it is reducible-as-type only at its own lower decoded level and
must lift UP) — is `DenoteKeyedCumulativityObstruction`: denote TYPE-reducibility cumulativity is model-obstructed
(a gap-universe-domain Π is codomain-blindly reducible at low levels, carrying no info upward).

In the BOUNDED relation cumulativity is FREE (`isReducibleBounded_cumulative`).  So
`piReducibleAsTypeFromNonUniformLevelMemberBounded` lifts each child from its own decoded level
(`universeMemberReducibleAsTypeAtDecodedLevelBounded`, the member→reducible-type decode) up to the Π output level
via `isReducibleBounded_cumulative`, then feeds `piReducibleAsTypeFromComponentReducibilityBounded`.  This closes
the non-uniform genFormationPi `piReducibleAsType` UNCONDITIONALLY — the exact case the bounded layer reaches.

## The five declarations

  * `piReducibleAsTypeFromNonUniformLevelMemberBounded` — **THE PAYOFF.**  Both children universe members at their
    OWN levels (each `≤ levelExpr`), each lifted to `denote levelExpr env` via free bounded cumulativity.  The
    general member discharge; closes the non-uniform case denote cannot.
  * `piReducibleAsTypeFromUniformLevelMemberBounded` — the uniform corollary (both children at `levelExpr`), the
    `Nat.le_refl` instance of the non-uniform one (the lifts are identities).
  * `piReducibleAsTypeFromUniverseDomainCodomainReducibilityBounded` — universe-DOMAIN anti-vacuity: a literal
    universe-code domain `Type@domainLevel` is reducible-as-type at the output level via `universeCode_isReducible\
    AtBounded`.  Unlike the ungated denote arm, the bounded `universeCode` arm carries the gate, so this takes the
    strict-below hypothesis `denote domainLevel env < denote levelExpr env`.
  * `piReducibleAsTypeFromUniverseCodeComponentsBounded` — both children universe codes — `Π (A : Type@a). Type@b`
    — discharged with only the two strict-below gates (the codomain is a closed code unchanged by `subst`/`subst0`).
  * `fundamentalGenFormationPiUniverseUniverseAtBounded` — **the FIRST fully-discharged bounded genFormationPi arm.**
    All three premises of `fundamentalGenFormationPiAtBounded` closed for `Π (A : Type@a). Type@b`: the domain member
    via `universeFormationMemberUnderClosingSubstitutionBounded`, the codomain SN via `noStep_universeCode`, the
    `piReducibleAsType` via the universe-code-components discharge.

## Zero-axiom verification

The payoff is two `isReducibleBounded_cumulative ∘ universeMemberReducibleAsTypeAtDecodedLevelBounded` legs fed to
the shipped connector; the uniform one is its `Nat.le_refl` instance; the universe-code ones distribute `subst` by
`subst_universeCodeCell` and discharge via the gated `universeCode_isReducibleAtBounded`; the universe-universe arm
routes through `fundamentalGenFormationPiAtBounded` with the three premises supplied (universe-formation member,
`noStep_universeCode` SN, universe-code discharge).  No induction, no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **THE PAYOFF — the non-uniform member discharge via free bounded cumulativity.**  `Π domain. codomain` is a
bound-reducible TYPE at the output level `denote levelExpr env` when each child is a bound-reducible MEMBER of its
own universe `Type@(domain/codomain)Level` whose decoded level is `≤ denote levelExpr env`.  Each member decodes to
a reducible TYPE at its OWN decoded level (`universeMemberReducibleAsTypeAtDecodedLevelBounded`), then lifts UP to
the Π output level via `isReducibleBounded_cumulative` (the free bounded cumulativity).  This closes the case where
a child is classified STRICTLY below the Π's output universe — the case `DenoteKeyedCumulativityObstruction` leaves
model-obstructed in the denote relation.  Feeds the connector `piReducibleAsTypeFromComponentReducibilityBounded`. -/
theorem piReducibleAsTypeFromNonUniformLevelMemberBounded {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainLevel codomainLevel levelExpr : LevelExpr)
    (domainFlag codomainFlag : UniverseFlag)
    (domainBelowBound : LevelExpr.denote domainLevel env < bound)
    (codomainBelowBound : LevelExpr.denote codomainLevel env < bound)
    (domainBelowOutput : LevelExpr.denote domainLevel env ≤ LevelExpr.denote levelExpr env)
    (codomainBelowOutput : LevelExpr.denote codomainLevel env ≤ LevelExpr.denote levelExpr env)
    (domainMember : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsReducibleMemberAtBounded env bound
          (universeCodeCell domainLevel domainFlag) (RawTerm.subst substitution domain))
    (codomainMember : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ argument : RawTerm targetScope,
          IsReducibleMemberAtBounded env (LevelExpr.denote levelExpr env)
            (RawTerm.subst substitution domain) argument →
          IsReducibleMemberAtBounded env bound
            (universeCodeCell codomainLevel codomainFlag)
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomain) argument)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env)
          (RawTerm.subst substitution (piTyCodeCell domain codomain)) :=
  piReducibleAsTypeFromComponentReducibilityBounded env bound context levelExpr
    (fun substitution envReducible =>
      isReducibleBounded_cumulative
        (universeMemberReducibleAsTypeAtDecodedLevelBounded
          (domainMember substitution envReducible) domainBelowBound)
        domainBelowOutput)
    (fun substitution envReducible argument argumentMember =>
      isReducibleBounded_cumulative
        (universeMemberReducibleAsTypeAtDecodedLevelBounded
          (codomainMember substitution envReducible argument argumentMember) codomainBelowBound)
        codomainBelowOutput)

/-- **The uniform member discharge (both children at the output level).**  The `Nat.le_refl` instance of
`piReducibleAsTypeFromNonUniformLevelMemberBounded`: when both children are classified at the Π's OWN output
universe `levelExpr`, the cumulativity lifts are identities, so the only side condition is `denote levelExpr env <
bound`.  Mirrors the denote `piReducibleAsTypeFromUniformLevelMember`; at bounded it is subsumed by the non-uniform
form, kept for the uniform-fragment FT assembly and parity. -/
theorem piReducibleAsTypeFromUniformLevelMemberBounded {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)} (levelExpr : LevelExpr)
    (domainFlag codomainFlag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < bound)
    (domainMember : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsReducibleMemberAtBounded env bound
          (universeCodeCell levelExpr domainFlag) (RawTerm.subst substitution domain))
    (codomainMember : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ argument : RawTerm targetScope,
          IsReducibleMemberAtBounded env (LevelExpr.denote levelExpr env)
            (RawTerm.subst substitution domain) argument →
          IsReducibleMemberAtBounded env bound
            (universeCodeCell levelExpr codomainFlag)
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomain) argument)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env)
          (RawTerm.subst substitution (piTyCodeCell domain codomain)) :=
  piReducibleAsTypeFromNonUniformLevelMemberBounded env bound context levelExpr levelExpr levelExpr
    domainFlag codomainFlag levelAbove levelAbove (Nat.le_refl _) (Nat.le_refl _) domainMember codomainMember

/-- **The universe-DOMAIN anti-vacuity discharge (bound-carrying).**  When the Π's domain is a literal universe code
`Type@domainLevel`, the domain is reducible-as-type at the output level via `universeCode_isReducibleAtBounded`.  The
bounded `universeCode` arm carries its gate (unlike the ungated denote anti-vacuity), so this takes the strict-below
hypothesis `denote domainLevel env < denote levelExpr env`.  The residual is isolated to the CODOMAIN premise. -/
theorem piReducibleAsTypeFromUniverseDomainCodomainReducibilityBounded {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    (domainLevel levelExpr : LevelExpr) (domainFlag : UniverseFlag) {codomain : RawTerm (scope + 1)}
    (domainStrictlyBelowOutput : LevelExpr.denote domainLevel env < LevelExpr.denote levelExpr env)
    (codomainReducibleAtDecoded : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ argument : RawTerm targetScope,
          IsReducibleMemberAtBounded env (LevelExpr.denote levelExpr env)
            (universeCodeCell domainLevel domainFlag) argument →
          IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env)
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomain) argument)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env)
          (RawTerm.subst substitution (piTyCodeCell (universeCodeCell domainLevel domainFlag) codomain)) :=
  piReducibleAsTypeFromComponentReducibilityBounded env bound context levelExpr
    (fun substitution _envReducible => by
      rw [subst_universeCodeCell]
      exact universeCode_isReducibleAtBounded env (LevelExpr.denote levelExpr env) domainLevel domainFlag
        domainStrictlyBelowOutput)
    codomainReducibleAtDecoded

/-- **Both children universe codes — `Π (A : Type@a). Type@b` — discharged via two strict-below gates.**  Both
children are universe codes anti-vacuously reducible-as-type at the output level; the codomain is a CLOSED universe
code unchanged by `subst`/`subst0`, so it is reducible at the output level for EVERY domain member.  Closes the
non-uniform `a ≠ b` case entirely via the gated anti-vacuity — the type-half witness that the obstruction is a
member-candidate phenomenon, not a type-reducibility one.  Corollary of `piReducibleAsTypeFromUniverseDomainCodomain\
ReducibilityBounded` with the codomain supplied by anti-vacuity. -/
theorem piReducibleAsTypeFromUniverseCodeComponentsBounded {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    (domainLevel codomainLevel levelExpr : LevelExpr) (domainFlag codomainFlag : UniverseFlag)
    (domainStrictlyBelowOutput : LevelExpr.denote domainLevel env < LevelExpr.denote levelExpr env)
    (codomainStrictlyBelowOutput : LevelExpr.denote codomainLevel env < LevelExpr.denote levelExpr env) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env)
          (RawTerm.subst substitution
            (piTyCodeCell (universeCodeCell domainLevel domainFlag)
              (universeCodeCell codomainLevel codomainFlag))) :=
  piReducibleAsTypeFromUniverseDomainCodomainReducibilityBounded env bound context domainLevel levelExpr domainFlag
    domainStrictlyBelowOutput
    (fun _substitution _envReducible argument _argumentInDomain => by
      rw [subst_universeCodeCell,
        show (universeCodeCell codomainLevel codomainFlag).subst0 argument
          = universeCodeCell codomainLevel codomainFlag from rfl]
      exact universeCode_isReducibleAtBounded env (LevelExpr.denote levelExpr env) codomainLevel codomainFlag
        codomainStrictlyBelowOutput)

/-- **The FIRST fully-discharged bounded genFormationPi arm — `Π (A : Type@a). Type@b`.**  All three premises of
`fundamentalGenFormationPiAtBounded` closed for the type-of-type-families former: the domain member via
`universeFormationMemberUnderClosingSubstitutionBounded` (`Type@a` is a member of `Type@(lsucc a)`), the codomain SN
via `noStep_universeCode` (the closed code is a normal form), and the `piReducibleAsType` via
`piReducibleAsTypeFromUniverseCodeComponentsBounded`.  The bound-carrying analogue of the denote
`fundamentalGenFormationPiUniverseUniverse`; the strict-below conditions on the inner levels are explicit (the
caller knows `levelExpr` is the Π's `lmax` of the children's classifying universes). -/
theorem fundamentalGenFormationPiUniverseUniverseAtBounded {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    (innerDomainLevel innerCodomainLevel levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < bound)
    (domainAbove : LevelExpr.denote (LevelExpr.lsucc innerDomainLevel) env < bound)
    (domainStrictlyBelowOutput : LevelExpr.denote innerDomainLevel env < LevelExpr.denote levelExpr env)
    (codomainStrictlyBelowOutput : LevelExpr.denote innerCodomainLevel env < LevelExpr.denote levelExpr env) :
    FundamentalConclusionAtBounded env bound context
      (piTyCodeCell (universeCodeCell innerDomainLevel flag) (universeCodeCell innerCodomainLevel flag))
      (universeCodeCell levelExpr flag) :=
  fundamentalGenFormationPiAtBounded env bound context (LevelExpr.lsucc innerDomainLevel) levelExpr flag
    levelAbove domainAbove
    (fun substitution _envReducible =>
      universeFormationMemberUnderClosingSubstitutionBounded env innerDomainLevel flag bound domainAbove substitution)
    (fun substitution _envReducible => by
      rw [subst_universeCodeCell]
      exact isStronglyNormalizing_of_noStep (fun _target => noStep_universeCode (innerCodomainLevel, flag)))
    (piReducibleAsTypeFromUniverseCodeComponentsBounded env bound context
      innerDomainLevel innerCodomainLevel levelExpr flag flag domainStrictlyBelowOutput codomainStrictlyBelowOutput)

end FX1Poly.Typed
