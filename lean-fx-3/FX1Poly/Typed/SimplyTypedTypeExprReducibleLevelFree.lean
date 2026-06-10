import FX1Poly.Core.ReducibleTypeWellFormed
import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.StrongNormalizationRenameForwardGeneral
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Typed.CellSubstitution
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/SimplyTypedTypeExprReducibleLevelFree
    — the domain supplier for the LEVEL-FREE simply-typed term fundamental theorem

The simply-typed term FT assembles over the level-free reducibility layer (see
`AbstractionNonDependentUnderSubstLevelFree` for why: the lambda binder extends `ReducibleEnv` from a single
member, so there is no all-levels universe wall).  Its lambda arm
(`IsReducibleMember.abstractionNonDependentUnderSubst`) needs the abstraction's DOMAIN to be a reducible
level-free TYPE under the closing substitution.  This file ships that domain supplier for the
directly-reducible type fragment.

  * `ReducibleType.nonDependentArrow` — the level-free non-dependent arrow type builder: from domain +
    codomain reducibility, the simple arrow `A → B` (code `piTyCodeCell domainCode (weaken codomainBase)`) is
    reducible.  The level-free twin of the stratified `IsReducibleTypeAtAllLevels.nonDependentArrow`.  Built
    from the dependent-arrow `ReducibleType.piType`: the per-argument codomain
    `subst0 (weaken codomainBase) argument` collapses to the constant `codomainBase`
    (`RawTerm.weaken_subst_singleton`), so the codomain candidate family is constant.

  * `IsReducibleTypeExprLF` — the directly-reducible simply-typed type expressions: a universe code `Type@e`,
    or a non-dependent arrow of such.  No type-variable leaves: a type variable's universe membership decodes
    only to `SN` in the level-free layer (`atNeutralClassifier`), NOT a `ReducibleType` — so a type-VARIABLE
    domain cannot supply a candidate level-free.  Excluding it confines the FT to the fragment that closes
    without the dual obstruction.

  * `IsReducibleTypeExprLF.reducibleUnderSubst` — the supplier proper: every such type expression substitutes
    to a directly-reducible level-free type under any closing substitution.  `universeCode` arm:
    `subst σ (Type@e) = Type@e` (`subst_universeCodeCell`), reducible by `IsReducibleType.universeCode`.
    `arrow` arm: `subst σ (A → B) = (subst σ A) → (subst σ B)` (`subst_piTyCodeCell` +
    `subst_lift_weaken_commute`), reducible by `ReducibleType.nonDependentArrow` on the two induction
    hypotheses.

This is the level-free analogue of the stratified `IsSimplyTypedTypeExpr.reducibleAtAllLevels`; together with
the lambda arm it leaves only the term judgment + `ReducibleEnv` assembly for the simply-typed term FT.

## Zero-axiom verification

`nonDependentArrow`: `ReducibleType.piType` + a `rw` by `RawTerm.weaken_subst_singleton`.  `reducibleUnderSubst`:
`induction` on the type-expression witness — `subst_universeCodeCell` + `IsReducibleType.universeCode`, and the
`subst_piTyCodeCell` / `subst_lift_weaken_commute` rewrite + `nonDependentArrow` on the induction hypotheses.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation StepStar

/-- **Level-free non-dependent arrow type builder.**  From domain reducibility and codomain reducibility, the
simple arrow `A → B` (code `piTyCodeCell domainCode (RawTerm.weaken codomainBase)`) is a reducible type at the
arrow candidate `fun f => ∀ argument, domainCandidate argument → codomainCandidate (appCell f argument)`.  The
level-free twin of the stratified `IsReducibleTypeAtAllLevels.nonDependentArrow`: built from the dependent
`ReducibleType.piType` with the per-argument codomain `subst0 (weaken codomainBase) argument` collapsing to the
constant `codomainBase` (`RawTerm.weaken_subst_singleton`). -/
theorem ReducibleType.nonDependentArrow {scope : Nat}
    {domainCode codomainBase : RawTerm scope}
    {domainCandidate codomainCandidate : RawTerm scope → Prop}
    (domainReducible : ReducibleType domainCode domainCandidate)
    (codomainReducible : ReducibleType codomainBase codomainCandidate) :
    ReducibleType (piTyCodeCell domainCode (RawTerm.weaken codomainBase))
      (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
        codomainCandidate (appCell functionTerm argument)) := by
  apply ReducibleType.piType (fun _argument => codomainCandidate) domainReducible
  intro argument _argumentInDomain
  rw [show RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase from
    RawTerm.weaken_subst_singleton codomainBase argument]
  exact codomainReducible

/-- **A level-free simply-typed type expression.**  A universe code `Type@levelExpr+flag`, or a non-dependent
arrow of type expressions — the directly-reducible types whose reducibility under any closing substitution is
supplied structurally (no type-variable leaves; a type variable decodes only to `SN` level-free). -/
inductive IsReducibleTypeExprLF {scope : Nat} : RawTerm scope → Prop
  | universeCode (levelExpr : LevelExpr) (flag : UniverseFlag) :
      IsReducibleTypeExprLF (universeCodeCell levelExpr flag)
  | arrow {domainCode codomainBase : RawTerm scope}
      (domainExpr : IsReducibleTypeExprLF domainCode)
      (codomainExpr : IsReducibleTypeExprLF codomainBase) :
      IsReducibleTypeExprLF (piTyCodeCell domainCode (RawTerm.weaken codomainBase))

/-- **The domain supplier for the level-free simply-typed term fundamental theorem.**  A reducible type
expression substitutes to a directly-reducible level-free type under any closing substitution — exactly the
domain reducibility the term FT's lambda arm (`IsReducibleMember.abstractionNonDependentUnderSubst`) consumes.
`universeCode` arm: substitution fixes the universe code, reducible by `IsReducibleType.universeCode`; `arrow`
arm: the substitution-commutation rewrite + `ReducibleType.nonDependentArrow` on the induction hypotheses. -/
theorem IsReducibleTypeExprLF.reducibleUnderSubst {scope targetScope : Nat}
    {typeExprCode : RawTerm scope} {substitution : RawTermSubst scope targetScope}
    (typeExpr : IsReducibleTypeExprLF typeExprCode) :
    IsReducibleType (RawTerm.subst substitution typeExprCode) := by
  induction typeExpr with
  | universeCode levelExpr flag =>
      rw [subst_universeCodeCell]
      exact IsReducibleType.universeCode levelExpr flag
  | arrow _domainExpr _codomainExpr domainInductiveHypothesis codomainInductiveHypothesis =>
      rename_i domainCode codomainBase
      have typeEq : RawTerm.subst substitution (piTyCodeCell domainCode (RawTerm.weaken codomainBase))
          = piTyCodeCell (RawTerm.subst substitution domainCode)
              (RawTerm.weaken (RawTerm.subst substitution codomainBase)) := by
        rw [subst_piTyCodeCell]
        exact congrArg (piTyCodeCell (RawTerm.subst substitution domainCode))
          (subst_lift_weaken_commute substitution codomainBase)
      rw [typeEq]
      obtain ⟨domainCandidate, domainReducible⟩ := domainInductiveHypothesis
      obtain ⟨codomainCandidate, codomainReducible⟩ := codomainInductiveHypothesis
      exact ⟨_, ReducibleType.nonDependentArrow domainReducible codomainReducible⟩

/-- **Forward strong normalization of a weakening.**  Weakening preserves strong normalization at every
scope — routed through the reflection-based Core primitive `weaken_isStronglyNormalizing_forward` (every
step of `weaken t` reflects to a source step, so the source's accessibility transfers).  This is scope-0
safe (a `weaken` at the closed scope has no total left inverse, so the inversion route fails there; the
forward reflection needs none).  The codomain-SN bridge the arrow arm of `stronglyNormalizingUnderSubst`
needs (`weaken (subst σ B)` is SN when `subst σ B` is). -/
theorem weaken_stronglyNormalizing {scope : Nat} {sourceTerm : RawTerm scope}
    (sourceTerminates : IsStronglyNormalizing sourceTerm) :
    IsStronglyNormalizing (RawTerm.weaken sourceTerm) :=
  weaken_isStronglyNormalizing_forward sourceTerminates

/-- **A reducible level-free type expression is strongly normalizing under any closing substitution.**  The
SN companion to `reducibleUnderSubst`: every `IsReducibleTypeExprLF` substitutes to a strongly normalizing
type code.  `universeCode` arm: `subst σ (Type@e) = Type@e` is a normal leaf (`noStep_universeCode`).  `arrow`
arm: the substituted Π former `piTyCodeCell (subst σ A) (weaken (subst σ B))` is SN by
`piTyCode_isStronglyNormalizing_of_domain_codomain` over the domain induction hypothesis and the weakened
codomain induction hypothesis (`weaken_stronglyNormalizing`).  This is the `domainAnnSN` the level-free
simply-typed term FT's lambda arm threads to the Church-style abstraction lemma. -/
theorem IsReducibleTypeExprLF.stronglyNormalizingUnderSubst {scope targetScope : Nat}
    {typeExprCode : RawTerm scope}
    {substitution : RawTermSubst scope targetScope}
    (typeExpr : IsReducibleTypeExprLF typeExprCode) :
    IsStronglyNormalizing (RawTerm.subst substitution typeExprCode) := by
  induction typeExpr with
  | universeCode levelExpr flag =>
      rw [subst_universeCodeCell]
      exact isStronglyNormalizing_of_noStep
        (fun _target step => noStep_universeCode (levelExpr, flag) step)
  | arrow _domainExpr _codomainExpr domainInductiveHypothesis codomainInductiveHypothesis =>
      rename_i domainCode codomainBase
      have typeEq : RawTerm.subst substitution (piTyCodeCell domainCode (RawTerm.weaken codomainBase))
          = piTyCodeCell (RawTerm.subst substitution domainCode)
              (RawTerm.weaken (RawTerm.subst substitution codomainBase)) := by
        rw [subst_piTyCodeCell]
        exact congrArg (piTyCodeCell (RawTerm.subst substitution domainCode))
          (subst_lift_weaken_commute substitution codomainBase)
      rw [typeEq]
      exact piTyCode_isStronglyNormalizing_of_domain_codomain
        domainInductiveHypothesis
        (weaken_stronglyNormalizing codomainInductiveHypothesis)

end FX1Poly.Typed
