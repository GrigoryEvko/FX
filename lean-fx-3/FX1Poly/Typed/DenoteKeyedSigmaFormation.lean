import FX1Poly.Typed.DenoteKeyedUniverseMembershipIntro
import FX1Poly.Typed.DenoteKeyedReducibilitySmoke
import FX1Poly.Typed.CellSubstitution
import FX1Poly.Core.StrongNormalizationConstructors

/-! # FX1Poly/Typed/DenoteKeyedSigmaFormation
    — the Σ-former case of the genFormationPi denote fundamental-theorem arm (SN-D5d; toward SN-043/#750)

`typingRuleDescOf` is `some` for EXACTLY two generators — `gen_piTyCode` and `gen_sigmaTyCode` (the dependent
type-formers; `HasTypeDesc.lean:94`).  So the grown engine's sole formation arm `HasTypeDescPi.genFormationPi`,
generic over `typingRuleDescOf generator = some rule`, is a TWO-CASE split, not a 194-way generic dispatch —
and the two cases close by DIFFERENT routes:

  * **Σ (`gen_sigmaTyCode`)** — reducible-as-a-type via the FREE neutral arm (`smoke_sigmaFormer_isReducible
    AtDenote`: a Σ former has no `WeakHeadStep`, so it is a reducible type at EVERY level with the strong-
    normalization candidate, no constraint on its children, NO threshold dependency).  This file.
  * **Π (`gen_piTyCode`)** — reducible-as-a-type via the dependent-arrow `piType` arm, which DOES constrain its
    domain to be reducible at the former's higher decoded output level: the threshold-drift residual #752.

This is the denote analogue of the fuel-route Σ arm `IsReducibleMemberAt.sigmaFormationUnderSubst`
(`ReducibleSemanticRules.lean:328`), targeting the DENOTE relation `IsReducibleMemberAtDenote` (not the fuel
`IsReducibleMemberAt`).  It is the FIRST genFormationPi denote-FT arm to close FULLY (both the strong-
normalization and the reducible-as-type conjunct), unconditional — the Σ case carries no threshold hypothesis,
exactly because its reducible-as-type half is the free neutral arm.

## The declaration

`sigmaFormationMemberAtDenote` — under a closing `substitution`, the Σ-type code `Σ domain. codomain` is a
denote-reducible MEMBER of its universe `Type@levelExpr` at any ambient `level` strictly above the decoded
classifier level, whenever its substituted domain and under-binder codomain are strongly normalizing (the
γ-closed strong-normalization induction hypotheses the telescope supplies).  The substituted former is
strongly normalizing (`sigmaTyCode_isStronglyNormalizing_of_domain_codomain` over the substituted children —
the substitution distributes over the Σ cell by `rfl`, the domain by `substitution`, the codomain by the
lift) AND a reducible type at the decoded level (`smoke_sigmaFormer_isReducibleAtDenote`, the free neutral
arm); `universeMembershipIntroAtDenote` packages the two into universe membership, `subst_universeCodeCell`
(`rfl`) leaving the closed universe classifier fixed.

## Zero-axiom verification

`rw [subst_universeCodeCell]` (the closed classifier), then `rw` the `rfl` substitution-distribution equation,
then `universeMembershipIntroAtDenote` on the substituted former's strong-normalization (two-child former-SN)
and its reducible-as-type (the shipped Σ-former smoke).  No induction, no `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked: depends on no axioms).
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The Σ-former case of the genFormationPi denote fundamental-theorem arm.**  Under a closing
`substitution`, the Σ-type code `Σ domain. codomain` is a denote-reducible MEMBER of its universe code
`Type@levelExpr` at any ambient `level` above the decoded classifier level, given its substituted domain and
under-binder codomain are strongly normalizing.  The substituted former is SN
(`sigmaTyCode_isStronglyNormalizing_of_domain_codomain`, the substitution distributing by `rfl`) and a
reducible type at the decoded level via the FREE neutral arm (`smoke_sigmaFormer_isReducibleAtDenote`, no
threshold dependency); `universeMembershipIntroAtDenote` packages membership and `subst_universeCodeCell`
fixes the closed classifier.  The denote analogue of `IsReducibleMemberAt.sigmaFormationUnderSubst`. -/
theorem sigmaFormationMemberAtDenote {scope targetScope : Nat} (env : Nat → Nat) (level : Nat)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (substitution : RawTermSubst scope targetScope)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (domainNormalizing : IsStronglyNormalizing (RawTerm.subst substitution domain))
    (codomainNormalizing :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) codomain)) :
    IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution (universeCodeCell levelExpr flag))
      (RawTerm.subst substitution
        (.mkGen .gen_sigmaTyCode () (.childCons domain (.childCons codomain .childNil)))) := by
  rw [subst_universeCodeCell]
  have substEq :
      RawTerm.subst substitution
          (.mkGen .gen_sigmaTyCode () (.childCons domain (.childCons codomain .childNil)))
        = .mkGen .gen_sigmaTyCode ()
            (.childCons (RawTerm.subst substitution domain)
              (.childCons (RawTerm.subst (RawTermSubst.lift substitution) codomain) .childNil)) := rfl
  rw [substEq]
  exact universeMembershipIntroAtDenote env levelExpr flag level
    (.mkGen .gen_sigmaTyCode ()
      (.childCons (RawTerm.subst substitution domain)
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) codomain) .childNil)))
    levelAbove
    (sigmaTyCode_isStronglyNormalizing_of_domain_codomain domainNormalizing codomainNormalizing)
    (smoke_sigmaFormer_isReducibleAtDenote env (LevelExpr.denote levelExpr env)
      (RawTerm.subst substitution domain) (RawTerm.subst (RawTermSubst.lift substitution) codomain))

end FX1Poly.Typed
