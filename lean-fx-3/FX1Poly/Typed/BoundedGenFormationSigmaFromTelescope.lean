import FX1Poly.Typed.BoundedGenFormationPiFromTelescope
import FX1Poly.Typed.CellSubstitution
import FX1Poly.Core.WeakHeadStepNormalForms

/-! # FX1Poly/Typed/BoundedGenFormationSigmaFromTelescope
    — the bounded `genFormationPi` recursor arm for the Σ former (the Σ twin of BFT-4)

This is the Σ-former minor-premise body of the bounded grown fundamental theorem (`HasTypeDescPi.rec`), the
data-former twin of `fundamentalGenFormationPiFromTelescopeAtBoundedSucc` (`BoundedGenFormationPiFromTelescope.\
lean`).  From the SAME telescope IH — the children's bound-reducibility under every closing substitution at the
former's decoded OUTPUT level `denote (lmaxAll [domainLevel, codomainLevel]) env` (the telescope is agnostic to
which former its two children assemble into) — it produces the `+1`-closing fundamental conclusion: the former
`sigmaTyCodeCell domain codomain` is a bound-reducible member of `Type@(lmaxAll …)`.

## Why the Σ arm is SIMPLER than the Π arm (the `neutral` classification)

`ReducibleTypeStepBounded` has a `piType` arm but NO `sigmaType` arm — a Σ former is classified by the `neutral`
arm: it is weak-head-normal (`WeakHeadStep.not_from_sigmaTyCode`), `gen_sigmaTyCode`-rooted (≠ `gen_piTyCode`,
≠ `gen_universeCode`), so its candidate is `IsStronglyNormalizing` (the SN-set), not a Σ-structured candidate.
Consequently the former's reducible-as-type-at-the-output-level needs ONLY former SN — NOT the per-component
cumulative lifts (`isReducibleBounded_cumulative ∘ universeMemberReducibleAsTypeAtDecodedLevelBounded` +
`piReducibleAtLevelFromComponentsBounded`) the Π arm needs.  The domain/codomain SN, the level-bound extraction,
and the var-0 codomain instantiation are IDENTICAL to the Π arm (they come off the shared telescope).  Members of
the Σ type being SN-only here (not pair-structured) is irrelevant for SN-043 — for canonicity the Σ data-candidate
(SN-057/059) is the separate, finer object.

## The assembly (all callees shipped)

`twoChildMembers` (BFT-3) projects the domain member (at `bound`) and the per-argument codomain member;
gate-extraction (`universeCodeReducibleAtBounded_belowBound`) reads `domainBelowBound` and (via
`variableZeroMemberOfBoundedUniverseMember`) `codomainBelowBound`; `levelMax_lt` gives the output `belowBound`;
`stronglyNormalizing_of_universeMemberAtBounded` gives the domain SN, `codomainOpenStronglyNormalizing_ofBounded\
FilledMember` the open codomain SN, and `sigmaTyCode_isStronglyNormalizing_of_domain_codomain` assembles the
former SN; the former's reducibility-as-type at the output level is the `neutral` arm of `ReducibleTypeStepBounded`
(candidate `IsStronglyNormalizing`).  `universeMembershipIntroAtBounded` closes it.

## Zero-axiom verification

One `intro` then a chain of shipped lemma applications plus three `rw` (`subst_sigmaTyCodeCell` twice,
`subst_universeCodeCell`) and two `show … by decide` defeq generator-disequalities; no induction, no `funext`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked: depends on no
axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The bounded `genFormationPi` recursor arm for the Σ former (two-child Σ former).**  From the telescope IH
(children bound-reducible under every closing substitution at the former's decoded output level), the former
`sigmaTyCodeCell domain codomain` is a `+1`-closing fundamental member of `Type@(lmaxAll [domainLevel,
codomainLevel])`.  The Σ twin of `fundamentalGenFormationPiFromTelescopeAtBoundedSucc`; the former's
reducible-as-type uses the `neutral` arm (SN candidate) since the relation has no `sigmaType` arm. -/
theorem fundamentalGenFormationSigmaFromTelescopeAtBoundedSucc {profile : PolyProfile} {scope : Nat}
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
      (sigmaTyCodeCell domain codomain)
      (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag) := by
  intro _targetScope substitution envReducible
  obtain ⟨domainMember, codomainMemberFn⟩ := (telescope substitution envReducible).twoChildMembers
  have domainBelowBound : LevelExpr.denote domainLevel env < bound := by
    obtain ⟨_domCand, domCandReducible, _domIn⟩ := domainMember
    exact universeCodeReducibleAtBounded_belowBound domCandReducible
  have domainBelowOutput := denote_domainLevel_le_lmaxAll_pair domainLevel codomainLevel env
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
  have sigmaSN : IsStronglyNormalizing (RawTerm.subst substitution (sigmaTyCodeCell domain codomain)) := by
    rw [subst_sigmaTyCodeCell]
    exact sigmaTyCode_isStronglyNormalizing_of_domain_codomain domainSN codomainSN
  have sigmaReducible :
      IsReducibleTypeAtBounded env (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
        (RawTerm.subst substitution (sigmaTyCodeCell domain codomain)) := by
    rw [subst_sigmaTyCodeCell]
    exact ⟨IsStronglyNormalizing,
      ReducibleTypeStepBounded.neutral
        (fun _reduct => WeakHeadStep.not_from_sigmaTyCode)
        (show Generator.gen_sigmaTyCode ≠ Generator.gen_piTyCode by decide)
        (show Generator.gen_sigmaTyCode ≠ Generator.gen_universeCode by decide)
        (show Generator.gen_sigmaTyCode ≠ Generator.gen_emptyCode by decide)
        (show Generator.gen_sigmaTyCode.isFlatDataCode = false by decide)⟩
  rw [subst_universeCodeCell]
  exact universeMembershipIntroAtBounded env (lmaxAll [domainLevel, codomainLevel]) flag bound
    (RawTerm.subst substitution (sigmaTyCodeCell domain codomain)) belowBound sigmaSN sigmaReducible

end FX1Poly.Typed
