import FX1Poly.Typed.ReducibleEnvTypeVariable
import FX1Poly.Typed.ReducibleEnvAtAllLevels
import FX1Poly.Typed.ReducibleTypeAtAllLevelsNonDependentArrow
import FX1Poly.Core.SubstPreservationProbes

/-! # FX1Poly/Typed/SimplyTypedTypeExprFT
    — the TYPE-LEVEL half of the simply-typed fundamental theorem

The simply-typed fundamental theorem (term FT) has a λ-introduction arm that needs the abstraction's DOMAIN
and CODOMAIN to be reducible TYPES under the closing substitution.  This file proves that obligation as a
self-contained theorem over a context-relative simply-typed TYPE-EXPRESSION judgment — the type-level half on
which the term FT's λ arm rests.

`IsSimplyTypedTypeExpr context` classifies the pure-STLC type expressions over a context: a type VARIABLE
(bound at a universe `Type@levelExpr+flag`), or a non-dependent arrow of type expressions.  No data-former
leaves: every free variable of such a type is a TYPE variable, so the type's reducibility comes ENTIRELY from
the environment — never from the open universe wall.

`reducibleAtAllLevels` is the FT: under an all-levels reducible closing environment, every such type expression
substitutes to an all-levels reducible type.

  * `typeVar` — `subst σ α = σ α`, reducible at every level by `ReducibleEnvAt.typeVariableReducible` applied at
    each level of the `ReducibleEnvAtAllLevels` environment (the universe-membership decode).  This is where the
    universe wall would otherwise bite (a type variable IS a member of `Type@e`) — and where it is sidestepped:
    the reducibility is READ OFF the environment, not derived through the fuel-`0` degeneracy.
  * `arrow` — `subst σ (A → B) = (subst σ A) → (subst σ B)` (`subst_piTyCodeCell` + `subst_lift_weaken_commute`),
    reducible by `IsReducibleTypeAtAllLevels.nonDependentArrowOfAllLevelsDomain` on the two induction hypotheses.

So the type-level FT is wall-free: the only place the wall could appear (a type variable's reducibility) is
discharged from the environment.  The remaining work toward the full simply-typed FT is the TERM judgment +
its assembly (var = `lookupReducible`, app = `applicationUnderSubst`, λ = `abstractionNonDependentUnderSubst`
fed this type-level FT for the domain/codomain).

## Zero-axiom verification

`induction` on the type-expression witness: the `typeVar` arm is `subst_var_reduces` + per-level
`typeVariableReducible`; the `arrow` arm is the substitution-commutation rewrite + `nonDependentArrowOfAllLevelsDomain`
on the induction hypotheses.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **A simply-typed type expression over a context.**  A type VARIABLE bound at a universe `Type@levelExpr+flag`,
or a non-dependent arrow of type expressions — the pure-STLC types whose free variables are all type-variables,
so their reducibility is supplied entirely by the environment (never by the universe wall). -/
inductive IsSimplyTypedTypeExpr {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) : RawTerm scope → Prop
  | typeVar (index : Fin scope) (levelExpr : LevelExpr) (flag : UniverseFlag)
      (lookupIsUniverse : context.lookup index = universeCodeCell levelExpr flag) :
      IsSimplyTypedTypeExpr context (variableCell index)
  | arrow {domainCode codomainBase : RawTerm scope}
      (domainExpr : IsSimplyTypedTypeExpr context domainCode)
      (codomainExpr : IsSimplyTypedTypeExpr context codomainBase) :
      IsSimplyTypedTypeExpr context (piTyCodeCell domainCode (RawTerm.weaken codomainBase))

/-- **The type-level fundamental theorem for the simply-typed fragment.**  Under an all-levels reducible
closing environment, every simply-typed type expression substitutes to a type reducible at all levels.  The
type-variable arm reads reducibility off the environment (the universe-membership decode, sidestepping the
wall); the arrow arm is the non-dependent-arrow reducibility on the two induction hypotheses.  This is the
domain/codomain reducibility the term FT's λ-introduction arm consumes. -/
theorem IsSimplyTypedTypeExpr.reducibleAtAllLevels {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {typeExprCode : RawTerm scope}
    {substitution : RawTermSubst scope targetScope}
    (envReducible : ReducibleEnvAtAllLevels context substitution)
    (typeExpr : IsSimplyTypedTypeExpr context typeExprCode) :
    IsReducibleTypeAtAllLevels (RawTerm.subst substitution typeExprCode) := by
  induction typeExpr with
  | typeVar index levelExpr flag lookupIsUniverse =>
      rw [show RawTerm.subst substitution (variableCell index) = substitution index from
        RawTerm.subst_var_reduces substitution index]
      intro level
      exact ReducibleEnvAt.typeVariableReducible index (envReducible level) lookupIsUniverse
  | arrow _domainExpr _codomainExpr domainInductiveHypothesis codomainInductiveHypothesis =>
      rename_i domainCode codomainBase
      have typeEq : RawTerm.subst substitution (piTyCodeCell domainCode (RawTerm.weaken codomainBase))
          = piTyCodeCell (RawTerm.subst substitution domainCode)
              (RawTerm.weaken (RawTerm.subst substitution codomainBase)) := by
        rw [subst_piTyCodeCell]
        exact congrArg (piTyCodeCell (RawTerm.subst substitution domainCode))
          (subst_lift_weaken_commute substitution codomainBase)
      rw [typeEq]
      exact IsReducibleTypeAtAllLevels.nonDependentArrowOfAllLevelsDomain
        domainInductiveHypothesis codomainInductiveHypothesis

end FX1Poly.Typed
