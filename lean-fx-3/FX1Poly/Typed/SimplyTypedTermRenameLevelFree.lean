import FX1Poly.Typed.SimplyTypedTermFundamentalLevelFree
import FX1Poly.Typed.SimplyTypedTypeExprClosureLevelFree
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.CellRenaming

/-! # FX1Poly/Typed/SimplyTypedTermRenameLevelFree
    — `SimplyTypedTermLF` is preserved by any context-respecting renaming (and its weakening corollary).

The subject-reduction arc's term-side substrate.  A simply-typed term survives any renaming `ρ` that
respects the contexts — i.e. sends each source binding's looked-up type to the corresponding target binding's
looked-up type (commuting with `rename`).  The substitution lemma (next step) needs exactly this for its
binder-lift: going under a λ, the already-substituted argument must be weakened into the extended context,
which is the `weakenUnderBinding` corollary below.

* `SimplyTypedTermLF.renameRespectingContext` — general renaming preservation, with the context-morphism
  condition quantified inside the conclusion so `induction typed` carries it through the motive.
* `SimplyTypedTermLF.weakenUnderBinding` — the corollary for extending the context by one fresh binding;
  its context condition holds definitionally (`fun _ => rfl`, via the `lookup_cons_succ` unfolder).

The proof mirrors `HasType.renameRespectingContext` but for the syntax-directed `SimplyTypedTermLF` (var/app/
lam, no conversion arm, so no Newman bridge):

* `var` — `rename_variableCell` then the context condition lands the renamed lookup.
* `app` — both subderivations rename by the IHs; a `functionType` equation (`rename_piTyCodeCell` +
  `rename_lift_weaken_commute` via `congrArg`) re-presents the renamed function type as
  `piTyCodeCell (rename ρ dom) (weaken (rename ρ cod))` so the `app` rule fires.
* `lam` — the body IH fires with the LIFTED renaming (`iterateLiftRaw ρ 1`) and the lifted context condition
  (`renameContextCondition_cons`); the body's type re-presents via `rename_lift_weaken_commute`; the `lam`
  rule's `IsReducibleTypeExprLF` premises on domain/codomain transport via `IsReducibleTypeExprLF.rename`.

## Zero-axiom verification

Composes the `rename_*Cell` cell-renaming bricks, `rename_lift_weaken_commute`, `renameContextCondition_cons`,
and `IsReducibleTypeExprLF.rename` — all zero-axiom.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe Foundation

/-- **`SimplyTypedTermLF` is preserved by any context-respecting renaming.**  A renaming `rawRenaming` that
sends each source binding's looked-up type to the target binding's looked-up type (commuting with `rename`)
carries the whole typing derivation across, renaming both subject and classifier. -/
theorem SimplyTypedTermLF.renameRespectingContext {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (typed : SimplyTypedTermLF sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      SimplyTypedTermLF targetContext
        (RawTerm.rename rawRenaming subject)
        (RawTerm.rename rawRenaming classifier) := by
  induction typed with
  | var index =>
      intro targetScope targetContext rawRenaming contextCondition
      rw [rename_variableCell, contextCondition index]
      exact SimplyTypedTermLF.var (rawRenaming index)
  | @app sourceScope sourceContext functionTerm argument domainCode codomainBase
      functionTyped argumentTyped ihFunction ihArgument =>
      intro targetScope targetContext rawRenaming contextCondition
      have functionRenamed := ihFunction targetContext rawRenaming contextCondition
      have argumentRenamed := ihArgument targetContext rawRenaming contextCondition
      have functionType :
          RawTerm.rename rawRenaming (piTyCodeCell domainCode (RawTerm.weaken codomainBase))
            = piTyCodeCell (RawTerm.rename rawRenaming domainCode)
                (RawTerm.weaken (RawTerm.rename rawRenaming codomainBase)) := by
        rw [rename_piTyCodeCell]
        exact congrArg (piTyCodeCell (RawTerm.rename rawRenaming domainCode))
          (rename_lift_weaken_commute rawRenaming codomainBase)
      rw [functionType] at functionRenamed
      rw [rename_appCell]
      exact SimplyTypedTermLF.app functionRenamed argumentRenamed
  | @lam sourceScope sourceContext body domainCode codomainBase
      domainExpr codomainExpr bodyTyped ihBody =>
      intro targetScope targetContext rawRenaming contextCondition
      have bodyRenamed := ihBody (targetContext.cons (RawTerm.rename rawRenaming domainCode))
        (iterateLiftRaw rawRenaming 1)
        (renameContextCondition_cons domainCode rawRenaming contextCondition)
      have bodyType :
          RawTerm.rename (iterateLiftRaw rawRenaming 1) (RawTerm.weaken codomainBase)
            = RawTerm.weaken (RawTerm.rename rawRenaming codomainBase) :=
        rename_lift_weaken_commute rawRenaming codomainBase
      rw [bodyType] at bodyRenamed
      rw [rename_lamCell]
      have resultType :
          RawTerm.rename rawRenaming (piTyCodeCell domainCode (RawTerm.weaken codomainBase))
            = piTyCodeCell (RawTerm.rename rawRenaming domainCode)
                (RawTerm.weaken (RawTerm.rename rawRenaming codomainBase)) := by
        rw [rename_piTyCodeCell]
        exact congrArg (piTyCodeCell (RawTerm.rename rawRenaming domainCode))
          (rename_lift_weaken_commute rawRenaming codomainBase)
      rw [resultType]
      exact SimplyTypedTermLF.lam (domainExpr.rename rawRenaming)
        (codomainExpr.rename rawRenaming) bodyRenamed

/-- **Typed weakening for the simply-typed fragment.**  Extend the context by one fresh binding, shifting
both subject and classifier by `RawRenaming.weaken`.  The corollary of `renameRespectingContext` whose
context condition holds definitionally (`weaken index` unfolds to `Fin.succ index`, the `cons` lookup fires
its successor arm).  This is the binder-lift the substitution lemma consumes. -/
theorem SimplyTypedTermLF.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (newBinding : RawTerm scope)
    (typed : SimplyTypedTermLF context subject classifier) :
    SimplyTypedTermLF (context.cons newBinding)
      (RawTerm.rename RawRenaming.weaken subject)
      (RawTerm.rename RawRenaming.weaken classifier) :=
  typed.renameRespectingContext (context.cons newBinding) RawRenaming.weaken (fun _ => rfl)

end FX1Poly.Typed
