import FX1Poly.Typed.SimplyTypedTermFundamentalLevelFree
import FX1Poly.Typed.SimplyTypedTypeExprClosureLevelFree
import FX1Poly.Typed.SimplyTypedTermRenameLevelFree
import FX1Poly.Typed.HasTypeDescPiSubstitution
import FX1Poly.Typed.CellSubstitution

/-! # FX1Poly/Typed/SimplyTypedTermSubstLevelFree
    — `SimplyTypedTermLF` is preserved by any well-typed substitution: the β-engine.

The subject-reduction arc's crux.  A simply-typed term survives any substitution `σ` that is well-typed for
the contexts — i.e. each source variable's substituent `σ i` is typed in the target context at the
substituted type of its binding.  Specialized to the single-variable substitution, this is the type
preservation β-reduction needs: `(λ. body) arg ↝ body[arg]` keeps its type.

* `SimplyTypedTermLF.substRespectingContext` — general substitution preservation, the
  substitution-morphism condition quantified inside the conclusion so `induction typed` carries it through
  the motive.
* `SimplyTypedTermLF.substituteUnderBinding` — the subst0 corollary (the β-engine): given `Γ, A ⊢ subject :
  classifier` and `Γ ⊢ argument : A`, the substituted `subject[argument]` has type `classifier[argument]`.

Mirrors `HasTypeDescPi.substRespectingContext` for the syntax-directed
`SimplyTypedTermLF` (var/app/lam, no conversion arm):

* `var` — `subst_variableCell` then the substitution-typing hypothesis lands the substituted variable.
* `app` — both subderivations substitute by the IHs; a `functionType` equation (`subst_piTyCodeCell` +
  `subst_lift_weaken_commute` via `congrArg`) re-presents the substituted function type so the `app` rule
  fires; the simply-typed (non-dependent) codomain means no `subst0`-commute is needed (unlike the dependent
  `piElim`).
* `lam` — the body IH fires with the LIFTED substitution and a 0/successor split of the lifted condition
  (position 0 is the fresh `var`; position k+1 is a weakened substituent via `weakenUnderBinding`, both
  crossing the binder by `subst_lift_weaken_commute`); the `lam` rule's `IsReducibleTypeExprLF` premises
  transport via `IsReducibleTypeExprLF.subst`.

This composes `IsReducibleTypeExprLF.subst` (type-expr closure) and
`SimplyTypedTermLF.weakenUnderBinding` (renaming preservation's weakening corollary).

## Zero-axiom verification

Composes the `subst_*Cell` substitution bricks, `subst_lift_weaken_commute`,
`subst_singleton_renameWeaken_cancel`, `IsReducibleTypeExprLF.subst`, and `weakenUnderBinding` — all
zero-axiom.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated
per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe Foundation

/-- **`SimplyTypedTermLF` is preserved by any well-typed substitution.**  A substitution `substitution` whose
substituent at each source variable is typed in the target context at the binding's substituted type carries
the whole typing derivation across, substituting both subject and classifier. -/
theorem SimplyTypedTermLF.substRespectingContext {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (typed : SimplyTypedTermLF sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        SimplyTypedTermLF targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      SimplyTypedTermLF targetContext
        (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier) := by
  induction typed with
  | var index =>
      intro targetScope targetContext substitution substitutionTyped
      rw [subst_variableCell]
      exact substitutionTyped index
  | @app sourceScope sourceContext functionTerm argument domainCode codomainBase
      functionTyped argumentTyped ihFunction ihArgument =>
      intro targetScope targetContext substitution substitutionTyped
      have functionSubst := ihFunction targetContext substitution substitutionTyped
      have argumentSubst := ihArgument targetContext substitution substitutionTyped
      have functionType :
          RawTerm.subst substitution (piTyCodeCell domainCode (RawTerm.weaken codomainBase))
            = piTyCodeCell (RawTerm.subst substitution domainCode)
                (RawTerm.weaken (RawTerm.subst substitution codomainBase)) := by
        rw [subst_piTyCodeCell]
        exact congrArg (piTyCodeCell (RawTerm.subst substitution domainCode))
          (subst_lift_weaken_commute substitution codomainBase)
      rw [functionType] at functionSubst
      rw [subst_appCell]
      exact SimplyTypedTermLF.app functionSubst argumentSubst
  | @lam sourceScope sourceContext body domainCode codomainBase
      domainExpr codomainExpr bodyTyped ihBody =>
      intro targetScope targetContext substitution substitutionTyped
      have bodySubst := ihBody (targetContext.cons (RawTerm.subst substitution domainCode))
        (RawTermSubst.lift substitution) ?liftedCondition
      · have bodyType :
            RawTerm.subst (RawTermSubst.lift substitution) (RawTerm.weaken codomainBase)
              = RawTerm.weaken (RawTerm.subst substitution codomainBase) :=
          subst_lift_weaken_commute substitution codomainBase
        rw [bodyType] at bodySubst
        rw [subst_lamCell]
        have resultType :
            RawTerm.subst substitution (piTyCodeCell domainCode (RawTerm.weaken codomainBase))
              = piTyCodeCell (RawTerm.subst substitution domainCode)
                  (RawTerm.weaken (RawTerm.subst substitution codomainBase)) := by
          rw [subst_piTyCodeCell]
          exact congrArg (piTyCodeCell (RawTerm.subst substitution domainCode))
            (subst_lift_weaken_commute substitution codomainBase)
        rw [resultType]
        exact SimplyTypedTermLF.lam (domainExpr.subst substitution)
          (codomainExpr.subst substitution) bodySubst
      case liftedCondition =>
        intro index
        obtain ⟨indexValue, indexBound⟩ := index
        cases indexValue with
        | zero =>
            rw [TypingContext.lookup_cons_zero, subst_lift_weaken_commute]
            exact SimplyTypedTermLF.var ⟨0, Nat.succ_pos targetScope⟩
        | succ k =>
            rw [TypingContext.lookup_cons_succ, subst_lift_weaken_commute]
            exact (substitutionTyped ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding
              (RawTerm.subst substitution domainCode)

/-- **Typed single-substitution (the β-engine).**  Substituting a well-typed `argument` for de Bruijn 0
preserves typing: given `Γ, A ⊢ subject : classifier` and `Γ ⊢ argument : A`, the substituted
`subject[argument]` has the substituted type `classifier[argument]` in `Γ`.  The corollary of
`substRespectingContext` at the singleton substitution; its side condition is a `Fin` 0/successor split
(position 0 returns `argument`, position k+1 a shifted variable), the looked-up binding types cancelling
their weakening against the singleton via `subst_singleton_renameWeaken_cancel`. -/
theorem SimplyTypedTermLF.substituteUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {argType : RawTerm scope}
    {subject classifier : RawTerm (scope + 1)} (argument : RawTerm scope)
    (typed : SimplyTypedTermLF (context.cons argType) subject classifier)
    (argumentTyped : SimplyTypedTermLF context argument argType) :
    SimplyTypedTermLF context
      (RawTerm.subst0 subject argument)
      (RawTerm.subst0 classifier argument) := by
  refine typed.substRespectingContext context (RawTermSubst.singleton argument) ?_
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show SimplyTypedTermLF context argument
        (RawTerm.subst (RawTermSubst.singleton argument)
          (RawTerm.rename RawRenaming.weaken argType))
      rw [subst_singleton_renameWeaken_cancel]
      exact argumentTyped
  | succ k =>
      show SimplyTypedTermLF context
          (variableCell ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)
        (RawTerm.subst (RawTermSubst.singleton argument)
          (RawTerm.rename RawRenaming.weaken
            (context.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)))
      rw [subst_singleton_renameWeaken_cancel]
      exact SimplyTypedTermLF.var ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩

end FX1Poly.Typed
