import LeanFX2.Foundation.Subst

/-! # SubstActsOnTy — Tier 3 / MEGA-Z2.A — `Subst level` instances of
the `ActsOnRawTerm` / `ActsOnTyVar` typeclasses.

`Ty.act` (defined in `Foundation/Ty.lean`) takes a Container with
`[Action Container]`, `[ActsOnRawTerm Container]`, and
`[ActsOnTyVar Container level]`.  The Container's instance of
`Action` ships in Z1.B (`Foundation/RawSubst.lean` and
`Foundation/Subst.lean`); the `ActsOnTyVar` / `ActsOnRawTerm`
instances are Z2.A additions.

For `RawRenaming`, both supplemental instances live in
`Foundation/Ty.lean` directly (no cyclic dependency since RawRenaming
is defined upstream in `Foundation/RawSubst.lean`).

For `Subst level`, the Container type is defined in
`Foundation/Subst.lean` (downstream of `Foundation/Ty.lean`).  Adding
the supplemental instances inside `Foundation/Subst.lean` would be
cleaner, but per the MEGA-Z2.A risk-management constraints
`Foundation/Subst.lean` is SEALED at Z1.B's boundary — no
modifications.  Hence this NEW file ships the `Subst level`
supplemental instances downstream of `Foundation/Subst.lean`.

The file does ONE thing: provide
* `instance : ActsOnRawTerm (Subst level)` for any `level`
* `instance ActsOnTyVarOfSubst (level : Nat) : ActsOnTyVar (Subst
  level) level`

so `Ty.act t (someSubst : Subst level src tgt)` typechecks and
reduces by `rfl` for representative ctors.
-/

namespace LeanFX2

/-! ## ActsOnRawTerm instance: Subst level.

A Subst's raw-term action delegates to `RawTerm.subst` over the
substitution's `forRaw` field.  The `level` parameter doesn't appear
in the operation — only in the Container's type.  Hence the instance
is parametric in `level`. -/

instance ActsOnRawTermOfSubst (level : Nat) :
    ActsOnRawTerm (Subst level) where
  actOnRawTerm := fun someSubst rawTerm => rawTerm.subst someSubst.forRaw

/-! ## ActsOnTyVar instance: Subst level.

A Subst's variable lookup consults `forTy`, which by definition
returns a `Ty level tgt` substituent.  The instance pins `level`
exactly to the Subst's level parameter. -/

instance ActsOnTyVarOfSubst (level : Nat) :
    ActsOnTyVar (Subst level) level where
  varToTy := fun someSubst position => someSubst.forTy position

/-! ## Smoke equivalences with existing `Ty.subst`.

The `Ty.act` engine over `Subst level` should produce the same
result as the existing `Ty.subst`.  The full equivalence theorem
`Ty.act_subst_eq_subst` lands in Z2.B (when `Ty.subst` is REDIRECTED
to `Ty.act`).  For Z2.A we ship the per-ctor `rfl` smokes
demonstrating the engine reduces correctly at leaf and binder
positions on a Subst Container. -/

theorem Ty.act_subst_unit_smoke
    {level scope targetScope : Nat}
    (someSubst : Subst level scope targetScope) :
    (Ty.unit (level := level) (scope := scope)).act someSubst = .unit := rfl

theorem Ty.act_subst_tyVar_smoke
    {level scope targetScope : Nat}
    (someSubst : Subst level scope targetScope)
    (position : Fin scope) :
    (Ty.tyVar (level := level) position).act someSubst =
      someSubst.forTy position := rfl

theorem Ty.act_subst_arrow_smoke
    {level scope targetScope : Nat}
    (someSubst : Subst level scope targetScope)
    (domainType codomainType : Ty level scope) :
    (Ty.arrow domainType codomainType).act someSubst =
      Ty.arrow (domainType.act someSubst) (codomainType.act someSubst) := rfl

theorem Ty.act_subst_piTy_smoke
    {level scope targetScope : Nat}
    (someSubst : Subst level scope targetScope)
    (domainType : Ty level scope)
    (codomainType : Ty level (scope + 1)) :
    (Ty.piTy domainType codomainType).act someSubst =
      Ty.piTy (domainType.act someSubst)
              (codomainType.act (Action.liftForTy someSubst)) := rfl

theorem Ty.act_subst_refine_smoke
    {level scope targetScope : Nat}
    (someSubst : Subst level scope targetScope)
    (baseType : Ty level scope)
    (predicate : RawTerm (scope + 1)) :
    (Ty.refine baseType predicate).act someSubst =
      Ty.refine (baseType.act someSubst)
                (ActsOnRawTerm.actOnRawTerm
                    (Action.liftForRaw someSubst) predicate) := rfl

theorem Ty.act_subst_id_smoke
    {level scope targetScope : Nat}
    (someSubst : Subst level scope targetScope)
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) :
    (Ty.id carrier leftEndpoint rightEndpoint).act someSubst =
      Ty.id (carrier.act someSubst)
            (ActsOnRawTerm.actOnRawTerm someSubst leftEndpoint)
            (ActsOnRawTerm.actOnRawTerm someSubst rightEndpoint) := rfl

theorem Ty.act_subst_universe_smoke
    {level scope targetScope : Nat}
    (someSubst : Subst level scope targetScope)
    (universeLevel : UniverseLevel)
    (levelLe : universeLevel.toNat + 1 ≤ level) :
    (Ty.universe (scope := scope) universeLevel levelLe).act someSubst =
      Ty.universe universeLevel levelLe := rfl

end LeanFX2
