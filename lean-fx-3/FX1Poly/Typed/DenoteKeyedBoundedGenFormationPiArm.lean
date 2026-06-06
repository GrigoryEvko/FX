import FX1Poly.Typed.DenoteKeyedBoundedPiIntroArm
import FX1Poly.Typed.DenoteKeyedBoundedFormerEngine
import FX1Poly.Typed.CellSubstitution
import FX1Poly.Core.StrongNormalizationConstructors

/-! # FX1Poly/Typed/DenoteKeyedBoundedGenFormationPiArm
    — the bound-carrying genFormationPi Π arm skeleton + single-level reducibility toolkit (#753 → SN-043)

The bound-carrying analogue of `DenoteKeyedSingleLevelPi` (the drift-free single-level Π toolkit) +
`DenoteKeyedGenFormationPiArm`'s premise-isolating arm + connector.  `Π domainCode codomainCode` is a
bound-reducible MEMBER of `Type@levelExpr`, the genFormationPi fundamental-theorem arm.

## The structure (and where the payoff lands)

The arm routes through the shipped former engine `fundamentalTypeFormerAtBounded`: it isolates the former's
TYPE-reducibility at the decoded output level (`piReducibleAsType`) as the single premise.  The connector
`piReducibleAsTypeFromComponentReducibilityBounded` reduces THAT to the children's reducibility at the decoded
level via the single-level building block `piReducibleAtLevelFromComponentsBounded` (the `piType` constructor with
the canonical member-predicate codomain, choice-free).  The children arrive either as universe MEMBERS — decoded
to reducible types by `universeMemberReducibleAsTypeAtDecodedLevelBounded` (the `.2`-projection twin of
`stronglyNormalizing_of_universeMemberAtBounded`, both off `universeMembershipBounded_levelIrrelevant`) — or as
universe CODES (anti-vacuously reducible).

The NON-UNIFORM case (a child classified strictly BELOW the output level, so it is reducible only at its lower
decoded level and must lift up) is the residual that the denote relation leaves MODEL-OBSTRUCTED
(`DenoteKeyedCumulativityObstruction`).  In the BOUNDED relation it CLOSES via `isReducibleBounded_cumulative`
(free cumulativity) — the payoff the bounded layer delivers.  This file ships the skeleton (arm +
connector + single-level blocks); the cumulativity discharge of the non-uniform case is the next brick.

## Zero-axiom verification

`piReducibleAtLevelFromComponentsBounded` is a single `piType` anonymous constructor with `reducibleMemberCandidate`
projections; `universeMemberReducibleAsTypeAtDecodedLevelBounded` is `deterministic` + `.2` projection (mirroring
the SN projection); the connector distributes `subst` by `subst_piTyCodeCell`; the arm routes through the former
engine, the Π-former SN being `piTyCode_isStronglyNormalizing_of_domain_codomain` (relation-agnostic Core) of the
CR1-discharged domain SN and the codomain SN premise.  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **Single-level Π type-reducibility from component reducibility (bound-carrying).**  `Π domainCode codomainCode`
is a bound-reducible TYPE at `bound` given `domainCode` reducible there and `codomainCode` reducible there for
every bound-reducible member of `domainCode`.  The codomain candidate is the canonical member-predicate
(`reducibleMemberCandidate`), keyed on membership — choice-free.  At ONE bound, so no member-stability / no
all-levels drift. -/
theorem piReducibleAtLevelFromComponentsBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainReducible : IsReducibleTypeAtBounded env bound domainCode)
    (codomainReducible : ∀ argument : RawTerm scope,
        IsReducibleMemberAtBounded env bound domainCode argument →
        IsReducibleTypeAtBounded env bound (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtBounded env bound
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  ⟨_, ReducibleTypeStepBounded.piType
    (fun argument => IsReducibleMemberAtBounded env bound (RawTerm.subst0 codomainCode argument))
    domainReducible.reducibleMemberCandidate
    (fun argument argumentInDomain =>
      (codomainReducible argument argumentInDomain).reducibleMemberCandidate)⟩

/-- **A universe member is a bound-reducible TYPE at the decoded level, directly (bound-carrying).**  A
bound-reducible member `typeCode` of `Type@levelExpr` (decoded level below the bound) is a bound-reducible TYPE at
the decoded level `denote levelExpr env`.  The `.2`-projection twin of `stronglyNormalizing_of_universeMemberAt\
Bounded`: align the member's candidate with the level-irrelevant bounded universe candidate via
`ReducibleTypeAtBounded.deterministic`, project the reducible-type conjunct. -/
theorem universeMemberReducibleAsTypeAtDecodedLevelBounded {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {typeCode : RawTerm scope}
    (memberOfUniverse : IsReducibleMemberAtBounded env bound
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) typeCode)
    (belowBound : LevelExpr.denote levelExpr env < bound) :
    IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env) typeCode := by
  obtain ⟨candidate, candidateReducible, candidateMember⟩ := memberOfUniverse
  have universeCandidateReducible :
      ReducibleTypeAtBounded env bound (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (fun member : RawTerm scope => IsStronglyNormalizing member ∧
          IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env) member) :=
    universeMembershipBounded_levelIrrelevant env bound levelExpr flag belowBound
  have pointwise := ReducibleTypeAtBounded.deterministic candidateReducible universeCandidateReducible
  exact ((pointwise typeCode).mp candidateMember).2

/-- **The bounded `piReducibleAsType` from component reducibility (the connector).**  Reduces the Π's
reducible-as-type-at-the-decoded-level to the children's reducibility at the decoded level — `subst` distributes
over the Π cell by `subst_piTyCodeCell`, then `piReducibleAtLevelFromComponentsBounded` closes.  The shape the
genFormationPi arm's `piReducibleAsType` premise consumes, parametric on how the children are supplied. -/
theorem piReducibleAsTypeFromComponentReducibilityBounded {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)} (levelExpr : LevelExpr)
    (domainReducibleAtDecoded : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env) (RawTerm.subst substitution domain))
    (codomainReducibleAtDecoded : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ argument : RawTerm targetScope,
          IsReducibleMemberAtBounded env (LevelExpr.denote levelExpr env)
            (RawTerm.subst substitution domain) argument →
          IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env)
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomain) argument)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env)
          (RawTerm.subst substitution (piTyCodeCell domain codomain)) := by
  intro _targetScope substitution envReducible
  rw [subst_piTyCodeCell]
  exact piReducibleAtLevelFromComponentsBounded env (LevelExpr.denote levelExpr env)
    (domainReducibleAtDecoded substitution envReducible)
    (codomainReducibleAtDecoded substitution envReducible)

/-- **The bounded `genFormationPi` Π fundamental-theorem arm (premise-isolating).**  From the domain's universe
membership (CR1-discharged to domain SN via `stronglyNormalizing_of_universeMemberAtBounded`), the codomain's
under-binder SN, and the Π former's bound-reducible-as-type at the decoded output level — all under every closing
substitution — `Π domain. codomain` satisfies the fundamental-theorem conclusion at `Type@levelExpr`.  Routes
through the former engine `fundamentalTypeFormerAtBounded`; the Π former SN is
`piTyCode_isStronglyNormalizing_of_domain_codomain` (relation-agnostic).  The `piReducibleAsType` premise — the
non-uniform A2 residual that is model-obstructed in denote — is supplied (in the bounded relation) via free
cumulativity, the next brick. -/
theorem fundamentalGenFormationPiAtBounded {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (bound : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainLevel levelExpr : LevelExpr) (flag : UniverseFlag)
    (belowBound : LevelExpr.denote levelExpr env < bound)
    (domainBelowBound : LevelExpr.denote domainLevel env < bound)
    (domainMember : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsReducibleMemberAtBounded env bound
          (universeCodeCell domainLevel flag) (RawTerm.subst substitution domain))
    (codomainSN : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) codomain))
    (piReducibleAsType : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsReducibleTypeAtBounded env (LevelExpr.denote levelExpr env)
          (RawTerm.subst substitution (piTyCodeCell domain codomain))) :
    FundamentalConclusionAtBounded env bound context
      (piTyCodeCell domain codomain) (universeCodeCell levelExpr flag) :=
  fundamentalTypeFormerAtBounded env bound context (piTyCodeCell domain codomain) levelExpr flag belowBound
    (fun substitution envReducible => by
      refine ⟨?_, piReducibleAsType substitution envReducible⟩
      rw [subst_piTyCodeCell]
      exact piTyCode_isStronglyNormalizing_of_domain_codomain
        (stronglyNormalizing_of_universeMemberAtBounded env bound domainLevel flag _ domainBelowBound
          (domainMember substitution envReducible))
        (codomainSN substitution envReducible))

end FX1Poly.Typed
