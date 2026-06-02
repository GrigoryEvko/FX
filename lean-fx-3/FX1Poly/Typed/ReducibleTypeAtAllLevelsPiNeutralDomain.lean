import FX1Poly.Typed.ReducibleTypeAtAllLevelsInduction

/-! # FX1Poly/Typed/ReducibleTypeAtAllLevelsPiNeutralDomain
    — level-irrelevance CLOSES for a Π type with a neutral / data-former domain

`ReducibleTypeAtAllLevelsInduction` reduced type-level level-irrelevance to its single `piArm` (the
Π-former case).  This file DISCHARGES that arm whenever the Π's DOMAIN is neutral or a data former (a
weak-head-normal code that is neither Π- nor universe-rooted).

The obstruction in the general Π arm is the domain-candidate level-MISMATCH: the codomain reducibility at
level `m` is quantified over the domain candidate at level `m`, which need not relate to the level-`n`
domain candidate the inductive hypothesis ranges over.  For a NEUTRAL / data-former domain that mismatch
DISSOLVES: such a domain denotes the SAME candidate — `IsStronglyNormalizing` — at EVERY level (the
`neutral` arm of `ReducibleTypeStep` is level-independent).  So the Π type can be rebuilt at every level
with a strongly-normalizing domain candidate and the FIXED canonical member-predicate for the codomain
(choice-free, via `IsReducibleTypeAt.reducibleMemberCandidate`), the codomain reducibility supplied by the
all-levels hypothesis on strongly-normalizing arguments.

Net: type-level level-irrelevance now holds UNCONDITIONALLY for every Π type whose domain is neutral / a
data former.  The residual obstruction is exactly a Π type whose domain is itself Π- or universe-rooted
(higher-order / type-polymorphic domains), where the domain candidate is genuinely level-dependent.

## Zero-axiom verification

`cases` on the level (to unfold `ReducibleTypeAt`), then the `piType` constructor with the `neutral` domain
arm (candidate `IsStronglyNormalizing`) and the canonical codomain candidate from
`reducibleMemberCandidate`.  No induction.  Verified `#print axioms` clean: no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Level-irrelevance for a Π type with a neutral / data-former domain.**  If the domain code is
weak-head-normal and neither Π- nor universe-rooted (a variable / stuck eliminator / data former, whose
reducible-type candidate is `IsStronglyNormalizing` at every level) and the codomain is reducible at all
levels for every strongly-normalizing argument, then the Π type is reducible at all levels — the domain's
level-independent candidate removes the domain-candidate mismatch that blocks the general Π arm. -/
theorem IsReducibleTypeAtAllLevels.piTypeOfNeutralDomain {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (domainNotPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (domainNotUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (codomainAllLevelsForStronglyNormalizingArgument :
      ∀ argument : RawTerm scope, IsStronglyNormalizing argument →
        IsReducibleTypeAtAllLevels (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllLevels
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) := by
  intro level
  cases level with
  | zero =>
      exact ⟨_, ReducibleTypeStep.piType
        (fun argument => IsReducibleMemberAt 0 (RawTerm.subst0 codomainCode argument))
        (ReducibleTypeStep.neutral domainWeakHeadNormal domainNotPiType domainNotUniverse)
        (fun argument stronglyNormalizingArgument =>
          ((codomainAllLevelsForStronglyNormalizingArgument argument
            stronglyNormalizingArgument) 0).reducibleMemberCandidate)⟩
  | succ predLevel =>
      exact ⟨_, ReducibleTypeStep.piType
        (fun argument => IsReducibleMemberAt (predLevel + 1) (RawTerm.subst0 codomainCode argument))
        (ReducibleTypeStep.neutral domainWeakHeadNormal domainNotPiType domainNotUniverse)
        (fun argument stronglyNormalizingArgument =>
          ((codomainAllLevelsForStronglyNormalizingArgument argument
            stronglyNormalizingArgument) (predLevel + 1)).reducibleMemberCandidate)⟩

/-- **Cons-arm universe-domain member-extension for a Π-type argument with a neutral / data-former
domain.**  Instantiating the type-polymorphic binder `Π (A : Type@e). …` by a function type `Π D C` whose
domain `D` is neutral / a data former closes (given the codomain's all-levels behaviour on
strongly-normalizing arguments): `piTypeOfNeutralDomain` discharges the type-level-irrelevance hypothesis of
`ofUniverseMemberUnderTypeLevelIrrelevance`. -/
theorem IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberPiNeutralDomainArgument {scope : Nat}
    {predLevel : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (domainNotPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (domainNotUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (codomainAllLevelsForStronglyNormalizingArgument :
      ∀ argument : RawTerm scope, IsStronglyNormalizing argument →
        IsReducibleTypeAtAllLevels (RawTerm.subst0 codomainCode argument))
    (member : IsReducibleMemberAt (predLevel + 1) (universeCodeCell levelExpr flag)
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))) :
    IsReducibleMemberAtAllPositiveLevels (universeCodeCell levelExpr flag)
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  IsReducibleMemberAtAllPositiveLevels.ofUniverseMemberUnderTypeLevelIrrelevance
    (fun _typeReducible =>
      IsReducibleTypeAtAllLevels.piTypeOfNeutralDomain domainWeakHeadNormal domainNotPiType
        domainNotUniverse codomainAllLevelsForStronglyNormalizingArgument)
    member

/-- **First concrete all-levels-reducibility witness for a DEPENDENT Π with a non-universe domain** —
`Π (x : var_index). Type@levelExpr` (a type-polymorphic-looking binder whose domain is a type VARIABLE, not a
universe) is reducible at all levels.  Validates the neutral-domain `piArm` discharger
(`piTypeOfNeutralDomain`) end-to-end on a real term: the domain `var_index` is neutral (`IsNeutral.var`, no
weak-head step, root `gen_var` ≠ Π/universe), and the codomain `Type@levelExpr` is reducible at all levels for
every (strongly-normalizing) argument via `ofUniverseCode` (it does not mention the bound variable, so
`subst0` leaves it a universe code).  This is the non-vacuity companion the all-levels Π machinery lacked: the
neutral/data-former branch of type-level level-irrelevance is genuinely inhabited.  The remaining open branch
is the UNIVERSE-domain Π (`Π (x : Type@e). x`), whose domain-member level-irrelevance is the documented
fixpoint requiring the mutual term/type fundamental theorem. -/
theorem allLevelsReducible_piOverNeutralVariableDomain {scope : Nat} (index : Fin scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsReducibleTypeAtAllLevels
      (piTyCodeCell (variableCell index) (universeCodeCell levelExpr flag)) := by
  apply IsReducibleTypeAtAllLevels.piTypeOfNeutralDomain
  · exact (IsNeutral.var index).noWeakHeadStep
  · show Generator.gen_var ≠ Generator.gen_piTyCode
    decide
  · show Generator.gen_var ≠ Generator.gen_universeCode
    decide
  · intro argument _stronglyNormalizing
    show IsReducibleTypeAtAllLevels (universeCodeCell levelExpr flag)
    exact IsReducibleTypeAtAllLevels.ofUniverseCode

end FX1Poly.Typed
