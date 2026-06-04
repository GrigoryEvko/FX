import FX1Poly.Typed.BoundedDomainInhabitant
import FX1Poly.Typed.BoundedCodomainOpenSN
import FX1Poly.Typed.DenoteKeyedBoundedTelescopeProjection
import FX1Poly.Typed.DenoteKeyedBoundedGenFormationPiDischarge
import FX1Poly.Typed.DenoteKeyedBoundedAssemblyBridge
import FX1Poly.Core.StrongNormalizationConstructors

/-! # FX1Poly/Typed/BoundedGenFormationPiFromTelescope
    — the bounded `genFormationPi` recursor arm: a two-child Π/Σ former is a fundamental member of its universe

This is the genFormationPi minor-premise body of the bounded grown fundamental theorem (`HasTypeDescPi.rec`),
specialized to the two-child dependent type-formers (Π / Σ, both with `universeFormerOutput`).  From the telescope
IH — the children's bound-reducibility under every closing substitution, at the former's decoded OUTPUT level
`denote (lmaxAll [domainLevel, codomainLevel]) env` — it produces the `+1`-closing fundamental conclusion: the
former `piTyCodeCell domain codomain` is a bound-reducible member of `Type@(lmaxAll …)`.

## The belowBound-threading resolution (why it builds the member INSIDE the ∀)

`fundamentalGenFormationPiAtBoundedSucc` / `fundamentalTypeFormerAtBoundedSucc` take the output `belowBound`
(`denote (lmaxAll …) env < bound`) as a FIXED parameter — but that fact is only obtainable from the children's
universe members, which need a closing substitution + reducible environment.  Rather than manufacture a canonical
environment to extract it once, this arm builds the universe member DIRECTLY inside the `∀ substitution
envReducible` (via `universeMembershipIntroAtBounded`), extracting every level bound per-substitution from the
telescope at the very environment it is proving for.  No canonical/identity environment is required.

## The assembly (all callees shipped)

For each closing substitution: `twoChildMembers` projects the domain member (at `bound`) and the per-argument
codomain member; `universeCodeReducibleAtBounded_belowBound` (gate-extraction) reads `domainBelowBound` and
(via the variable-0 inhabitant `variableZeroMemberOfBoundedUniverseMember`) `codomainBelowBound`; `levelMax_lt`
gives the output `belowBound`; the domain SN is `stronglyNormalizing_of_universeMemberAtBounded`, the open codomain
SN is `codomainOpenStronglyNormalizing_ofBoundedFilledMember`, and `piTyCode_isStronglyNormalizing_of_domain_\
codomain` assembles the former SN; the former's reducibility-as-type at the output level is
`piReducibleAtLevelFromComponentsBounded` fed the two children lifted from their own decoded levels to the output
by free bounded cumulativity (`isReducibleBounded_cumulative` + the `denote_*_le_lmaxAll_pair` bounds) — the exact
non-uniform cumulativity the whole bounded refactor was built for.  `universeMembershipIntroAtBounded` closes it.

## Zero-axiom verification

One `intro` then a chain of shipped lemma applications and two `rw` (`subst_piTyCodeCell`,
`subst_universeCodeCell`); no induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The bounded `genFormationPi` recursor arm (two-child Π/Σ former).**  From the telescope IH (children
bound-reducible under every closing substitution at the former's decoded output level), the former
`piTyCodeCell domain codomain` is a `+1`-closing fundamental member of `Type@(lmaxAll [domainLevel,
codomainLevel])`.  Builds the universe member inside the `∀`, extracting the level bounds per-substitution and
lifting the children to the output level by free bounded cumulativity. -/
theorem fundamentalGenFormationPiFromTelescopeAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (telescope : ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        TelescopeReducibleAtBounded env bound
          (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env) flag 0 2 substitution
          [domainLevel, codomainLevel]
          (.childCons domain (.childCons codomain .childNil))) :
    FundamentalConclusionAtBoundedSucc env bound context
      (piTyCodeCell domain codomain)
      (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag) := by
  intro _targetScope substitution envReducible
  obtain ⟨domainMember, codomainMemberFn⟩ := (telescope substitution envReducible).twoChildMembers
  have domainBelowBound : LevelExpr.denote domainLevel env < bound := by
    obtain ⟨_domCand, domCandReducible, _domIn⟩ := domainMember
    exact universeCodeReducibleAtBounded_belowBound domCandReducible
  have domainBelowOutput := denote_domainLevel_le_lmaxAll_pair domainLevel codomainLevel env
  have codomainBelowOutput := denote_codomainLevel_le_lmaxAll_pair domainLevel codomainLevel env
  have variableZeroMember :=
    variableZeroMemberOfBoundedUniverseMember domainMember domainBelowBound domainBelowOutput
  have codomainMemberAtVariableZero := codomainMemberFn _ variableZeroMember
  have codomainBelowBound : LevelExpr.denote codomainLevel env < bound := by
    obtain ⟨_codCand, codCandReducible, _codIn⟩ := codomainMemberAtVariableZero
    exact universeCodeReducibleAtBounded_belowBound codCandReducible
  have belowBound : LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env < bound :=
    levelMax_lt domainBelowBound codomainBelowBound
  have domainSN :=
    stronglyNormalizing_of_universeMemberAtBounded env bound domainLevel flag _ domainBelowBound domainMember
  have codomainSN := codomainOpenStronglyNormalizing_ofBoundedFilledMember codomainMemberAtVariableZero
  have piSN : IsStronglyNormalizing (RawTerm.subst substitution (piTyCodeCell domain codomain)) := by
    rw [subst_piTyCodeCell]
    exact piTyCode_isStronglyNormalizing_of_domain_codomain domainSN codomainSN
  have domainReducibleAtOutput :
      IsReducibleTypeAtBounded env (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
        (RawTerm.subst substitution domain) :=
    isReducibleBounded_cumulative
      (universeMemberReducibleAsTypeAtDecodedLevelBounded domainMember domainBelowBound)
      domainBelowOutput
  have codomainReducibleAtOutput :
      ∀ argument : RawTerm (_targetScope + 1),
        IsReducibleMemberAtBounded env (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
          (RawTerm.subst substitution domain) argument →
        IsReducibleTypeAtBounded env (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
          (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomain) argument) :=
    fun argument argumentMember =>
      isReducibleBounded_cumulative
        (universeMemberReducibleAsTypeAtDecodedLevelBounded
          (codomainMemberFn argument argumentMember) codomainBelowBound)
        codomainBelowOutput
  have piReducible :
      IsReducibleTypeAtBounded env (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
        (RawTerm.subst substitution (piTyCodeCell domain codomain)) := by
    rw [subst_piTyCodeCell]
    exact piReducibleAtLevelFromComponentsBounded env
      (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
      domainReducibleAtOutput codomainReducibleAtOutput
  rw [subst_universeCodeCell]
  exact universeMembershipIntroAtBounded env (lmaxAll [domainLevel, codomainLevel]) flag bound
    (RawTerm.subst substitution (piTyCodeCell domain codomain)) belowBound piSN piReducible

end FX1Poly.Typed
