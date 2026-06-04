import FX1Poly.Typed.DenoteKeyedUniverseMembershipIntro
import FX1Poly.Typed.DenoteKeyedSigmaFromChildMembers
import FX1Poly.Typed.HasTypeSubstitution
import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Typed.DenoteKeyedSingleLevelPi

/-! # FX1Poly/Typed/DenoteKeyedGenFormationPiArm
    — the genFormationPi Π fundamental-theorem arm (premise-isolating; SN-D5d toward SN-043/#750)

The Π case of the denote fundamental theorem's `genFormationPi` arm, completing the 2-case split {Π, Σ} of
`typingRuleDescOf` (the Σ case is `fundamentalGenFormationSigmaAtDenote`, `DenoteKeyedGenFormationSigmaArm.lean`).
Like the Σ arm and the shipped binder arm `fundamentalPiIntroAtDenote`, the children's fundamental-theorem data
arrive as universal premises; the arm assembles the conclusion `FundamentalConclusionAtDenote`.

Π differs from Σ in ONE place: its reducible-as-type half is NOT the free neutral arm (a Π former's members are
functions, not strong-normalization-only) — it routes through the dependent-arrow `piType` candidate, which
constrains the domain to be reducible at the former's higher decoded OUTPUT level.  That is the #752
threshold-drift residual, and (matching the premise-isolating discipline) it is carried here as the explicit
`piReducibleAsType` premise.  Everything else is identical to the Σ arm:
  * **domain SN** — FREE by denote CR1 (`stronglyNormalizing_of_universeMemberAtDenote`) on the domain's universe
    membership;
  * **codomain SN** — the under-binder `subst (lift σ) codomain` SN, the deferred premise whose production needs
    var-0 mining at the binder-weakened scope = the Kripke-obstructed denote renaming-closure (SN-040);
  * the Π former's strong normalization is `piTyCode_isStronglyNormalizing_of_domain_codomain` over the
    substituted children (the substitution distributing by `subst_piTyCodeCell`).

So both genFormationPi branches are now premise-complete, with the two #672-family walls cleanly ISOLATED: the
codomain-SN production (denote SN-040, shared by Π and Σ) and the Π reducible-as-type (#752, Π-only).

## The declaration

`fundamentalGenFormationPiAtDenote` — routes through the shipped former engine `fundamentalTypeFormerAtDenote`
(which isolates `formerReducible = SN ∧ reducible-as-type`): the SN conjunct is `piTyCode_isStronglyNormalizing_
of_domain_codomain` of the CR1-discharged domain SN and the codomain SN premise; the reducible-as-type conjunct
is the `piReducibleAsType` (#752) premise.

## Zero-axiom verification

`fundamentalTypeFormerAtDenote` applied to a `formerReducible` that, per substitution, pairs the Π former SN
(`rw [subst_piTyCodeCell]` then `piTyCode_isStronglyNormalizing_of_domain_codomain` on the CR1 domain SN + the
codomain SN premise) with the `piReducibleAsType` premise.  No induction, no `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked: depends on no axioms).
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The genFormationPi Π fundamental-theorem arm (premise-isolating).**  From the domain's universe membership
(CR1-discharged to domain SN), the codomain's under-binder SN, and the Π former's reducible-as-type at the
decoded output level (the #752 threshold residual, isolated as a premise) — all under every closing substitution
— `Π domain. codomain` satisfies the fundamental-theorem conclusion at `Type@levelExpr`.  Routes through the
former engine `fundamentalTypeFormerAtDenote`; the Π former SN is `piTyCode_isStronglyNormalizing_of_domain_
codomain`.  The Π twin of `fundamentalGenFormationSigmaAtDenote`, completing the genFormationPi 2-case split. -/
theorem fundamentalGenFormationPiAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainLevel levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (domainAbove : LevelExpr.denote domainLevel env < level)
    (domainMember : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleMemberAtDenote env level
          (universeCodeCell domainLevel flag) (RawTerm.subst substitution domain))
    (codomainSN : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) codomain))
    (piReducibleAsType : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env)
          (RawTerm.subst substitution (piTyCodeCell domain codomain))) :
    FundamentalConclusionAtDenote env level context
      (piTyCodeCell domain codomain) (universeCodeCell levelExpr flag) :=
  fundamentalTypeFormerAtDenote env level context (piTyCodeCell domain codomain) levelExpr flag levelAbove
    (fun substitution envReducible => by
      refine ⟨?_, piReducibleAsType substitution envReducible⟩
      rw [subst_piTyCodeCell]
      exact piTyCode_isStronglyNormalizing_of_domain_codomain
        (stronglyNormalizing_of_universeMemberAtDenote env level domainLevel flag _ domainAbove
          (domainMember substitution envReducible))
        (codomainSN substitution envReducible))

/-- **Discharge `fundamentalGenFormationPiAtDenote`'s `piReducibleAsType` premise from the children's
reducibility at the decoded output level.**  The `piReducibleAsType` premise (the #752-shaped Π reducible-as-type
at `denote levelExpr env`) is reduced to the more PRIMITIVE children's reducibility AT THAT decoded level — which
the fundamental-theorem recursion naturally supplies (the domain child is a universe member, reducible-as-type at
the decoded level by `universeMemberReducibleAsTypeAtDecodedLevel`; the codomain child is reducible at the
decoded level under the var-0-extended environment, the `subst0 (subst (lift σ) codomain) argument` shape via the
subst-lift commutation).  Routes through the drift-free single-level `piReducibleAtLevelFromComponents` after
distributing the substitution by `subst_piTyCodeCell`.  SINGLE level (the decoded output level, above all
internal thresholds) ⟹ NO all-levels low-level drift — this sidesteps the #752 all-levels piArm for the
genFormationPi reducible-as-type half. -/
theorem piReducibleAsTypeFromComponentReducibility {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)} (levelExpr : LevelExpr)
    (domainReducibleAtDecoded : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) (RawTerm.subst substitution domain))
    (codomainReducibleAtDecoded : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        ∀ argument : RawTerm targetScope,
          IsReducibleMemberAtDenote env (LevelExpr.denote levelExpr env)
            (RawTerm.subst substitution domain) argument →
          IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env)
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomain) argument)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env)
          (RawTerm.subst substitution (piTyCodeCell domain codomain)) := by
  intro _targetScope substitution envReducible
  rw [subst_piTyCodeCell]
  exact piReducibleAtLevelFromComponents env (LevelExpr.denote levelExpr env)
    (domainReducibleAtDecoded substitution envReducible)
    (codomainReducibleAtDecoded substitution envReducible)

/-- **Discharge `piReducibleAsType` from the children's universe-MEMBERSHIPS for the fully-uniform Π fragment.**
The fully-uniform Π `Π (A : Type@levelExpr). (B : Type@levelExpr)` — domain AND codomain classified at the SAME
universe `levelExpr` as the Π's own output (`levelExpr = lmaxAll [levelExpr, levelExpr]`) — has its
`piReducibleAsType` premise dischargeable WITHOUT any level lift.  Each child arrives from the fundamental-theorem
recursion as a reducible MEMBER of `Type@levelExpr` (the natural FT output), and a member of `Type@levelExpr`
decodes to a reducible TYPE at `denote levelExpr env` directly via `universeMemberReducibleAsTypeAtDecodedLevel`
— the decoded level is exactly the Π's level, so NO cumulativity is needed.  Composes
`piReducibleAsTypeFromComponentReducibility` (the connector) with `universeMemberReducibleAsTypeAtDecodedLevel`
on BOTH children.

This closes the fully-uniform fragment of `fundamentalGenFormationPiAtDenote`'s `piReducibleAsType`.  The
remaining NON-uniform cases — where `levelExpr = lmaxAll [domainLevel, codomainLevel]` STRICTLY exceeds one
child's classifying universe (so that child is reducible only at its lower decoded level and must lift UP to
`denote levelExpr env`) — are the level-bounded TYPE-reducibility cumulativity residual
(`IsReducibleTypeAtDenote env lowerLevel D → IsReducibleTypeAtDenote env levelExpr D` for `lowerLevel ≤ levelExpr`,
both above `D`'s internal universe thresholds), which is genuinely a multi-lemma effort (a universe-level-bound
predicate threaded through substitution-by-a-bounded-member), NOT a drift the member-stability route closes. -/
theorem piReducibleAsTypeFromUniformLevelMember {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)} (levelExpr : LevelExpr)
    (domainFlag codomainFlag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (domainMember : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleMemberAtDenote env level
          (universeCodeCell levelExpr domainFlag) (RawTerm.subst substitution domain))
    (codomainMember : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        ∀ argument : RawTerm targetScope,
          IsReducibleMemberAtDenote env (LevelExpr.denote levelExpr env)
            (RawTerm.subst substitution domain) argument →
          IsReducibleMemberAtDenote env level
            (universeCodeCell levelExpr codomainFlag)
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomain) argument)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env)
          (RawTerm.subst substitution (piTyCodeCell domain codomain)) :=
  piReducibleAsTypeFromComponentReducibility env level context levelExpr
    (fun substitution envReducible =>
      universeMemberReducibleAsTypeAtDecodedLevel (domainMember substitution envReducible) levelAbove)
    (fun substitution envReducible argument argumentMember =>
      universeMemberReducibleAsTypeAtDecodedLevel
        (codomainMember substitution envReducible argument argumentMember) levelAbove)

end FX1Poly.Typed
