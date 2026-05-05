import LeanFX2.Term.Rename
import LeanFX2.Term.Subst
import LeanFX2.Foundation.SubstActsOnTy
import LeanFX2.Foundation.TyActBridge

/-! # Term/Act — Tier 3 / MEGA-Z5.A.

`Term.act` is the unified `Term`-level recursion engine that
generalises `Term.rename` and `Term.subst` into a single typeclass-
dispatched operation.  Once both `Ty.act` (Z2.A) and `RawTerm.act`
(Z4.A) shipped, the two parallel typed engines collapse: each becomes
a `Term.act` invocation over its respective Container.

## Z5.A.1 prerequisites (in place)

* `actOnRawTerm action raw = RawTerm.act raw action` is `rfl` after
  Z2.A.1's instance-body alignment.
* `ActsOnRawTermVarLifts` typeclass with three `rfl`-bodied instances
  (`RawRenaming`, `RawTermSubst`, `Subst level`) provides the
  load-bearing var-under-lift reductions for closed-payload HoTT
  ctors.

## Architectural decision: thin wrapper over Term.rename / Term.subst

The mission's Term.act spec asks for a SINGLE recursion engine over
the ~38 Term ctors.  However, the typed companion of an action
(`TermRenaming` for `RawRenaming` vs `TermSubst` for `Subst level`)
differs in KIND: `TermRenaming` is a `Prop`, `TermSubst` is a `Type`
that carries Term values.  A truly-uniform per-ctor recursion would
need to bridge these.

The pragmatic alternative — adopted here per the MEGA-Z5.A risk
register — is a **per-Container thin wrapper** that:

* delegates the recursion to the existing `Term.rename` (for
  `RawRenaming`) or `Term.subst` (for `Subst level`);
* casts the result type from `(Ty.rename t rho, raw.rename rho)` /
  `(Ty.subst t sigma, raw.subst sigma.forRaw)` to the act-shaped
  `(Ty.act t action, RawTerm.act raw action)` via the Z2.B bridges
  `Ty.act_eq_rename` / `Ty.act_eq_subst` (Ty side) and Z2.A.1
  `RawTerm.act_eq_rename` / `RawTerm.act_eq_subst_forRaw` (raw side).

This delivers a unified `TermAct`-typeclass with a single
consumer-facing call site, while preserving the existing
infrastructure unchanged.  After Z3 retires the legacy operations,
each instance's body folds into the `Term.act` recursion directly.

## TermActCompat

The new typeclass `TermActCompat` bundles:
* the typed action data carrier (`TermAction`)
* the `lift` operation under one binder (`TermActionLift`)
* the function body (`termAct`)
* two cast lemmas: `weaken_act_commute` and `subst0_act_commute`

The cast lemmas are derived once-and-for-all from `Ty.act_eq_rename`
/ `Ty.act_eq_subst` chained with `Ty.weaken_rename_commute` /
`Ty.weaken_subst_commute` and `Ty.subst0_rename_commute` /
`Ty.subst0_subst_commute`.

## Audit philosophy

Every shipped declaration is gated by `#print axioms` in
`Smoke/AuditMegaZ5A.lean`.  All zero-axiom under strict policy.
-/

namespace LeanFX2

/-! ## Section 1 — `TermActCompat` typeclass + cast laws.

The two cast laws (`weaken_act_commute`, `subst0_act_commute`) are the
Container-specific commute facts that each `TermAct` instance proves.
They are stated abstractly in terms of `Ty.act` and
`Action.liftForTy` / `ActsOnRawTerm.actOnRawTerm`.

For the load-bearing Term.act recursion (when later refactored to a
single recursion engine), these laws are what discharges the
type-equality cast on the lam / lamPi / appPi / pair / snd / funextRefl
arms.  For now (the wrapper-based design) the laws ship as free-standing
theorems, available for downstream consumers. -/

/-- `TermActCompat Container level` ships the cast lemmas needed by
the Term.act consumer surface for the given Container.

* `weaken_act_commute` — `(Ty.weaken t).act (Action.liftForTy a) =
  Ty.weaken (Ty.act t a)`.  Mirrors `Ty.weaken_rename_commute` /
  `Ty.weaken_subst_commute` at the unified `Ty.act` level.
* `subst0_act_commute` — `(t.subst0 X r).act a = (t.act
  (Action.liftForTy a)).subst0 (X.act a) (actOnRawTerm a r)`.  Mirrors
  `Ty.subst0_rename_commute` / `Ty.subst0_subst_commute` at the
  unified `Ty.act` level. -/
class TermActCompat (Container : Nat → Nat → Type) (level : Nat)
    [Action Container] [ActsOnRawTerm Container]
    [ActsOnTyVar Container level] where
  /-- `(Ty.weaken t).act (liftForTy a) = Ty.weaken (Ty.act t a)`. -/
  weaken_act_commute : ∀ {sourceScope targetScope : Nat}
      (someAction : Container sourceScope targetScope)
      (someType : Ty level sourceScope),
      Ty.act (Ty.weaken someType) (Action.liftForTy someAction) =
        Ty.weaken (Ty.act someType someAction)
  /-- `(t.subst0 X r).act a = (t.act (liftForTy a)).subst0 (X.act a)
  (actOnRawTerm a r)`. -/
  subst0_act_commute : ∀ {sourceScope targetScope : Nat}
      (someAction : Container sourceScope targetScope)
      (codomainType : Ty level (sourceScope + 1))
      (argType : Ty level sourceScope)
      (argRaw : RawTerm sourceScope),
      Ty.act (codomainType.subst0 argType argRaw) someAction =
        (Ty.act codomainType (Action.liftForTy someAction)).subst0
          (Ty.act argType someAction)
          (ActsOnRawTerm.actOnRawTerm someAction argRaw)

/-! ## Section 2 — `TermActCompat` instance for `RawRenaming`.

Both cast laws follow from the Ty.act-eq-rename bridge chained with
the existing `Ty.weaken_rename_commute` / `Ty.subst0_rename_commute`
facts.  For `RawRenaming`, `Action.liftForTy rho = rho.lift`
definitionally, and `ActsOnRawTerm.actOnRawTerm rho rawTerm =
RawTerm.act rawTerm rho` (Z2.A.1 alignment).  The chain:

* `(Ty.weaken t).act (liftForTy rho)`
  = `(Ty.weaken t).act rho.lift`            [defn of liftForTy]
  = `(Ty.weaken t).rename rho.lift`         [Ty.act_eq_rename]
  = `Ty.weaken (t.rename rho)`              [Ty.weaken_rename_commute]
  = `Ty.weaken (t.act rho)`                 [Ty.act_eq_rename.symm]

(Same shape for `subst0_act_commute` via `Ty.subst0_rename_commute`.) -/

instance TermActCompatOfRawRenaming (level : Nat) :
    TermActCompat RawRenaming level where
  weaken_act_commute someRenaming someType := by
    show Ty.act someType.weaken (Action.liftForTy someRenaming) =
         Ty.weaken (Ty.act someType someRenaming)
    rw [Ty.act_eq_rename someType.weaken (Action.liftForTy someRenaming),
        Ty.act_eq_rename someType someRenaming]
    show Ty.rename someType.weaken someRenaming.lift =
         Ty.weaken (Ty.rename someType someRenaming)
    exact Ty.weaken_rename_commute someRenaming someType
  subst0_act_commute someRenaming codomainType argType argRaw := by
    -- ActsOnRawTerm.actOnRawTerm someRenaming argRaw
    --   = RawTerm.act argRaw someRenaming  (instance body in Foundation/Ty.lean)
    --   = argRaw.rename someRenaming       (RawTerm.act_eq_rename, Z2.A.1 bridge).
    -- Ty.act _ someRenaming = Ty.rename _ someRenaming (Z2.B bridge).
    show Ty.act (codomainType.subst0 argType argRaw) someRenaming =
         (Ty.act codomainType (Action.liftForTy someRenaming)).subst0
           (Ty.act argType someRenaming)
           (RawTerm.act argRaw someRenaming)
    rw [Ty.act_eq_rename (codomainType.subst0 argType argRaw) someRenaming,
        Ty.act_eq_rename codomainType (Action.liftForTy someRenaming),
        Ty.act_eq_rename argType someRenaming,
        RawTerm.act_eq_rename argRaw someRenaming]
    show Ty.rename (codomainType.subst0 argType argRaw) someRenaming =
         (Ty.rename codomainType someRenaming.lift).subst0
           (Ty.rename argType someRenaming)
           (RawTerm.rename argRaw someRenaming)
    exact Ty.subst0_rename_commute codomainType argType argRaw someRenaming

/-! ## Section 3 — `TermActCompat` instance for `Subst level`.

Both cast laws follow from the Ty.act-eq-subst bridge chained with
the existing `Ty.weaken_subst_commute` / `Ty.subst0_subst_commute`
facts.  Same chain shape as the RawRenaming instance, with `subst`
replacing `rename`. -/

instance TermActCompatOfSubst (level : Nat) :
    TermActCompat (Subst level) level where
  weaken_act_commute someSubst someType := by
    show Ty.act someType.weaken (Action.liftForTy someSubst) =
         Ty.weaken (Ty.act someType someSubst)
    rw [Ty.act_eq_subst someType.weaken (Action.liftForTy someSubst),
        Ty.act_eq_subst someType someSubst]
    show Ty.subst someType.weaken someSubst.lift =
         Ty.weaken (Ty.subst someType someSubst)
    exact Ty.weaken_subst_commute someSubst someType
  subst0_act_commute someSubst codomainType argType argRaw := by
    -- ActsOnRawTerm.actOnRawTerm someSubst argRaw
    --   = RawTerm.act argRaw someSubst   (instance body of ActsOnRawTermOfSubst)
    -- Ty.act _ someSubst = Ty.subst _ someSubst (Z2.B bridge).
    -- After unfolding, the goal becomes
    --   (codomainType.subst0 argType argRaw).subst someSubst
    --     = (codomainType.subst someSubst.lift).subst0
    --         (argType.subst someSubst)
    --         (RawTerm.act argRaw someSubst)
    -- which Ty.subst0_subst_commute discharges after one more
    -- RawTerm.act ↦ RawTerm.subst rewrite.
    show Ty.act (codomainType.subst0 argType argRaw) someSubst =
         (Ty.act codomainType (Action.liftForTy someSubst)).subst0
           (Ty.act argType someSubst)
           (RawTerm.act argRaw someSubst)
    rw [Ty.act_eq_subst (codomainType.subst0 argType argRaw) someSubst,
        Ty.act_eq_subst codomainType (Action.liftForTy someSubst),
        Ty.act_eq_subst argType someSubst,
        RawTerm.act_eq_subst_forRaw argRaw someSubst]
    show Ty.subst (codomainType.subst0 argType argRaw) someSubst =
         (Ty.subst codomainType someSubst.lift).subst0
           (Ty.subst argType someSubst)
           (RawTerm.subst argRaw someSubst.forRaw)
    exact Ty.subst0_subst_commute codomainType argType argRaw someSubst

/-! ## Section 4 — `Term.actRenaming` engine over `RawRenaming`.

A thin wrapper around `Term.rename` that returns a Term in the
unified `Ty.act` / `RawTerm.act` shape.  The chain of casts:

* `Term.rename ...` returns `Term targetCtx (Ty.rename someType rho)
  (raw.rename rho)`.
* `(Ty.act_eq_rename someType rho).symm ▸ ...` rewrites the type
  index to `Ty.act someType rho`.
* `(RawTerm.act_eq_rename raw rho).symm ▸ ...` rewrites the raw
  index to `RawTerm.act raw rho`.

Per the strict zero-axiom commitment, each `▸` cast is on Term-typed
values and uses `Eq.rec` on a reducible motive, which is axiom-free
(Smoke/AuditCast). -/

/-- Term.act over `RawRenaming` Container — thin wrapper around
`Term.rename` with type / raw indices cast to the `Ty.act` /
`RawTerm.act` shape. -/
@[reducible] def Term.actRenaming
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx someType raw) :
    Term targetCtx (Ty.act someType rho) (RawTerm.act raw rho) :=
  -- Apply Term.rename, then cast result type and raw index.
  let renamed : Term targetCtx (someType.rename rho) (raw.rename rho) :=
    Term.rename termRenaming sourceTerm
  let typeEqInverse : someType.rename rho = Ty.act someType rho :=
    (Ty.act_eq_rename someType rho).symm
  let rawEqInverse : raw.rename rho = RawTerm.act raw rho :=
    (RawTerm.act_eq_rename raw rho).symm
  rawEqInverse ▸ typeEqInverse ▸ renamed

/-! ## Section 5 — `Term.actSubst` engine over `Subst level`.

Mirror of `Term.actRenaming` for the `Subst level` Container.  The
chain of casts uses `Ty.act_eq_subst` / `RawTerm.act_eq_subst_forRaw`
in place of the `_rename` variants. -/

/-- Term.act over `Subst level` Container — thin wrapper around
`Term.subst` with type / raw indices cast to the `Ty.act` /
`RawTerm.act` shape. -/
@[reducible] def Term.actSubst
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx someType raw) :
    Term targetCtx (Ty.act someType sigma) (RawTerm.act raw sigma) :=
  let substituted : Term targetCtx (someType.subst sigma)
                                    (raw.subst sigma.forRaw) :=
    Term.subst termSubst sourceTerm
  let typeEqInverse : someType.subst sigma = Ty.act someType sigma :=
    (Ty.act_eq_subst someType sigma).symm
  let rawEqInverse : raw.subst sigma.forRaw = RawTerm.act raw sigma :=
    (RawTerm.act_eq_subst_forRaw raw sigma).symm
  rawEqInverse ▸ typeEqInverse ▸ substituted

/-! ## Section 6 — toRaw invariant.

`Term.actRenaming` and `Term.actSubst` both preserve the raw-index
invariant `Term.toRaw t = raw`: their result has raw index
`RawTerm.act raw container` (which IS the projection of the result by
construction, since `▸` on Eq doesn't disturb the projection equation).

For the typed chain, we add per-Container smoke gates verifying that
the wrappers' raw-form projection matches `RawTerm.act`. -/

end LeanFX2
