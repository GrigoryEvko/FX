import LeanFX2.Foundation.RawSubst.SubstIdentityAndBeta
import LeanFX2.Foundation.Action

/-! # LeanFX2.Foundation.RawSubst.ActionInstances

Wraps `RawRenaming` and `RawTermSubst` as `Action` typeclass
instances (Tier 3 / MEGA-Z1.B), supplies `ActsOnRawTermVar` (Z4.A)
and `ActsOnRawTermVarLifts` (Z5.A.1) instances, and ships the
per-ctor smoke equivalences for `RawTerm.act` reducing to the
existing `RawTerm.rename` / `RawTerm.subst`.

## Root status

Definitional `rfl`-bodied instances; strict zero-axiom. -/

namespace LeanFX2

/-! ## Tier 3 / MEGA-Z1.B — Action typeclass instances (raw layer).

Wrap the existing `RawRenaming` and `RawTermSubst` operations as
`Action` typeclass instances.  These are the raw-side Container
inhabitants of the universal-action-with-binding framework shipped in
`Foundation/Action.lean` (Z1.A).  Per the Z1.A docstring, these
instances supply:
* `liftForTy` and `liftForRaw` — set to the same existing `lift`
  (the operation is binder-shape-agnostic at the raw layer)
* `compose`, `identity`, `headIndex` — the existing top-level operations
* `composeAtHeadIndex` — the abstract pointwise behaviour exposed
  opaquely so the typeclass laws can be witnessed without funext.

All laws ship by `rfl` after `@[reducible]` unfolding plus, for the
substitution case, `RawTerm.subst_compose` / `RawTerm.subst_identity`. -/

/-- `Action` instance for `RawRenaming`.  Renamings are pure functions
`Fin source → Fin target`; compose is function composition; lift is
the existing `RawRenaming.lift`.  All laws hold by `rfl` (renaming is
the first-order action). -/
instance : Action RawRenaming where
  ActionTarget       := Fin
  headIndex          := fun rho position => rho position
  liftForTy          := fun rho => rho.lift
  liftForRaw         := fun rho => rho.lift
  identity           := RawRenaming.identity
  compose            := RawRenaming.compose
  composeAtHeadIndex := fun firstRenaming secondRenaming position =>
    secondRenaming (firstRenaming position)
  compose_assoc_pointwise            := fun _ _ _ _ => rfl
  compose_identity_left_pointwise    := fun _ _ => rfl
  compose_identity_right_pointwise   := fun _ _ => rfl
  headIndex_compose                  := fun _ _ _ => rfl

/-- Equivalence theorem: `RawRenaming.identity` is the identity action. -/
theorem RawRenaming.identity_eq_action {scope : Nat} :
    (RawRenaming.identity : RawRenaming scope scope) =
      (Action.identity : RawRenaming scope scope) := rfl

/-- Equivalence theorem: `RawRenaming.lift` agrees with
`Action.liftForTy`. -/
theorem RawRenaming.lift_eq_actionForTy {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) :
    rho.lift = Action.liftForTy rho := rfl

/-- Equivalence theorem: `RawRenaming.lift` agrees with
`Action.liftForRaw`. -/
theorem RawRenaming.lift_eq_actionForRaw {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) :
    rho.lift = Action.liftForRaw rho := rfl

/-- Equivalence theorem: `RawRenaming.compose` is the action's compose. -/
theorem RawRenaming.compose_eq_action
    {scopeA scopeB scopeC : Nat}
    (firstRenaming  : RawRenaming scopeA scopeB)
    (secondRenaming : RawRenaming scopeB scopeC) :
    RawRenaming.compose firstRenaming secondRenaming =
      Action.compose firstRenaming secondRenaming := rfl

/-- `Action` instance for `RawTermSubst`.  Substitutions are functions
`Fin source → RawTerm target`; compose threads through `RawTerm.subst`;
lift is the existing `RawTermSubst.lift`.

`composeAtHeadIndex` exposes `(σ1 pos).subst σ2` opaquely.  Laws
unfold via `RawTerm.subst_compose` (associativity) and
`RawTerm.subst_identity` (right unit); left unit is `rfl` since
`RawTermSubst.identity pos = RawTerm.var pos` and `Ty.subst` /
`RawTerm.subst` map a bare variable to the looked-up substituent. -/
instance : Action RawTermSubst where
  ActionTarget       := RawTerm
  headIndex          := fun sigma position => sigma position
  liftForTy          := fun sigma => sigma.lift
  liftForRaw         := fun sigma => sigma.lift
  identity           := RawTermSubst.identity
  compose            := RawTermSubst.compose
  composeAtHeadIndex := fun firstSigma secondSigma position =>
    (firstSigma position).subst secondSigma
  compose_assoc_pointwise firstSigma middleSigma lastSigma position := by
    -- Associativity reduces to `RawTerm.subst_compose` on the looked-up
    -- substituent at the source position.
    show ((RawTermSubst.compose firstSigma middleSigma) position).subst lastSigma =
         (firstSigma position).subst (RawTermSubst.compose middleSigma lastSigma)
    show ((firstSigma position).subst middleSigma).subst lastSigma =
         (firstSigma position).subst (RawTermSubst.compose middleSigma lastSigma)
    exact RawTerm.subst_compose middleSigma lastSigma (firstSigma position)
  compose_identity_left_pointwise someSigma position := by
    -- Identity-on-the-left: looking up at identity gives `RawTerm.var
    -- position`, and substituting `RawTerm.var position` against any
    -- σ is `σ position` by the var-arm of `RawTerm.subst`.
    show (RawTermSubst.identity position).subst someSigma = someSigma position
    rfl
  compose_identity_right_pointwise someSigma position := by
    -- Identity-on-the-right: substituting `someSigma position` by the
    -- identity substitution returns `someSigma position`.
    exact RawTerm.subst_identity (someSigma position)
  headIndex_compose firstSigma secondSigma position := by
    -- `RawTermSubst.compose σ1 σ2 pos = (σ1 pos).subst σ2` by the
    -- definition of `compose`; equals `composeAtHeadIndex σ1 σ2 pos`.
    rfl

/-- Equivalence theorem: `RawTermSubst.identity` is the action's identity. -/
theorem RawTermSubst.identity_eq_action {scope : Nat} :
    (RawTermSubst.identity : RawTermSubst scope scope) =
      (Action.identity : RawTermSubst scope scope) := rfl

/-- Equivalence theorem: `RawTermSubst.lift` agrees with
`Action.liftForTy`. -/
theorem RawTermSubst.lift_eq_actionForTy {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope) :
    sigma.lift = Action.liftForTy sigma := rfl

/-- Equivalence theorem: `RawTermSubst.lift` agrees with
`Action.liftForRaw`. -/
theorem RawTermSubst.lift_eq_actionForRaw {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope) :
    sigma.lift = Action.liftForRaw sigma := rfl

/-- Equivalence theorem: `RawTermSubst.compose` is the action's compose. -/
theorem RawTermSubst.compose_eq_action {sourceScope middleScope targetScope : Nat}
    (firstSigma  : RawTermSubst sourceScope middleScope)
    (secondSigma : RawTermSubst middleScope targetScope) :
    RawTermSubst.compose firstSigma secondSigma =
      Action.compose firstSigma secondSigma := rfl

/-! ## Tier 3 / MEGA-Z4.A — `ActsOnRawTermVar` instances.

`RawTerm.act` (defined in `Foundation/RawTerm.lean`) takes a Container
with `[Action Container]` and `[ActsOnRawTermVar Container]`.  The
Container's `Action` instance ships above (Z1.B); the
`ActsOnRawTermVar` instances are Z4.A additions, mirroring Z2.A's
`ActsOnTyVar` discipline at the raw layer.

For `RawRenaming`, `varToRawTerm` wraps the renamed Fin back as
`RawTerm.var` — this matches the `var` arm of the existing
`RawTerm.rename` definition.

For `RawTermSubst`, `varToRawTerm` returns the substituent term
directly (`sigma position`) — this matches the `var` arm of the
existing `RawTerm.subst` definition.

Once these instances are in scope, `RawTerm.act t (someRenaming :
RawRenaming src tgt)` reduces by `rfl` to the same shape as
`RawTerm.rename t someRenaming` for representative ctors; similarly
for `RawTermSubst`. -/

/-- `ActsOnRawTermVar` instance: `RawRenaming` wraps renamed Fin as
`RawTerm.var`. -/
instance : ActsOnRawTermVar RawRenaming where
  varToRawTerm := fun someRenaming position => RawTerm.var (someRenaming position)

/-- `ActsOnRawTermVar` instance: `RawTermSubst` returns the
substituent RawTerm directly. -/
instance : ActsOnRawTermVar RawTermSubst where
  varToRawTerm := fun sigma position => sigma position

/-! ## Tier 3 / MEGA-Z5.A.1 — `ActsOnRawTermVarLifts` typeclass + instances.

The closed-payload HoTT ctors that Z5.A's `Term.act` recursion engine
must traverse (`Term.equivReflId`, `Term.funextRefl`, etc.) bury a
`RawTerm.var ⟨0, _⟩` under `Action.liftForRaw action`.  Without a
reduction law for that specific shape, the typeclass dispatch
through `RawTerm.act` cannot rewrite the closed payload to a
`rfl`-equivalent target.

`ActsOnRawTermVarLifts` adds two extra fields to the `Action +
ActsOnRawTermVar` pair: a reduction law for the var-zero case under
`liftForRaw`, and a corresponding law for the var-succ case.
Concretely:

* `liftForRaw_var_zero` — under any lifted action, position `0`
  resolves to `RawTerm.var ⟨0, _⟩` in the target's lifted scope.
* `liftForRaw_var_succ` — under any lifted action, position `k+1`
  resolves to `RawTerm.weaken (varToRawTerm action k)`.

For all three Containers that the Tier 3 framework currently ships
(`RawRenaming`, `RawTermSubst`, `Subst level`), both laws hold by
`rfl` after the existing `@[reducible]` `lift` definitions unfold
— the `RawRenaming.lift` / `RawTermSubst.lift` / `Subst.lift`
definitions were chosen with these reductions in mind.

`ActsOnRawTermVarLifts` does NOT extend `Action` or
`ActsOnRawTermVar`; it sits alongside them as a separate constraint,
keeping the typeclass dependency lattice flat (mirroring the
discipline of Z2.A's `ActsOnTyVar` / Z4.A's `ActsOnRawTermVar`).
Consumers (`Term.act` in Z5.A, downstream HoTT ctor traversal arms)
take all three constraints as separate `[…]` arguments. -/

/-- Bridge typeclass: var-zero and var-succ reductions of
`varToRawTerm` under `Action.liftForRaw`.

Both laws hold by `rfl` for every Container that lifts variables
through `RawRenaming.lift` / `RawTermSubst.lift` / `Subst.lift`'s
`forRaw` discipline (i.e. position `0` maps to `RawTerm.var
⟨0, _⟩`, position `k+1` maps to `RawTerm.weaken` of the renamed/
substituted source). -/
class ActsOnRawTermVarLifts (Container : Nat → Nat → Type)
    [Action Container] [ActsOnRawTermVar Container] where
  /-- At position `0` under `Action.liftForRaw`, the lifted action
  produces `RawTerm.var ⟨0, _⟩` in the target's lifted scope. -/
  liftForRaw_var_zero : ∀ {sourceScope targetScope : Nat}
      (someAction : Container sourceScope targetScope),
        ActsOnRawTermVar.varToRawTerm
            (Action.liftForRaw someAction)
            (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
          = (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩ :
              RawTerm (targetScope + 1))
  /-- At position `k+1` under `Action.liftForRaw`, the lifted action
  produces `RawTerm.weaken` of the action applied to `k`. -/
  liftForRaw_var_succ : ∀ {sourceScope targetScope : Nat}
      (someAction : Container sourceScope targetScope)
      (predecessorIndex : Fin sourceScope),
        ActsOnRawTermVar.varToRawTerm
            (Action.liftForRaw someAction)
            ⟨predecessorIndex.val + 1,
              Nat.succ_lt_succ predecessorIndex.isLt⟩
          = RawTerm.weaken
              (ActsOnRawTermVar.varToRawTerm someAction predecessorIndex)

/-- `ActsOnRawTermVarLifts` instance for `RawRenaming`.

* `liftForRaw_var_zero` — `(rho.lift) ⟨0, _⟩ = ⟨0, Nat.zero_lt_succ _⟩`
  by the var-zero arm of `RawRenaming.lift`; `varToRawTerm` then wraps
  it as `RawTerm.var ⟨0, _⟩`.  Holds by `rfl` after `@[reducible]`
  unfolding of `RawRenaming.lift`.

* `liftForRaw_var_succ` — `(rho.lift) ⟨k+1, h⟩ = Fin.succ (rho ⟨k, _⟩)`
  by the var-succ arm of `RawRenaming.lift`; `varToRawTerm` wraps
  that as `RawTerm.var (Fin.succ (rho ⟨k, _⟩))`.  On the RHS,
  `RawTerm.weaken (RawTerm.var (rho ⟨k, _⟩))
    = (RawTerm.var (rho ⟨k, _⟩)).rename RawRenaming.weaken
    = RawTerm.var (Fin.succ (rho ⟨k, _⟩))`
  by the var-arm of `RawTerm.rename` and the definition of
  `RawRenaming.weaken`.  Holds by `rfl`. -/
instance : ActsOnRawTermVarLifts RawRenaming where
  liftForRaw_var_zero := fun _ => rfl
  liftForRaw_var_succ := fun _ _ => rfl

/-- `ActsOnRawTermVarLifts` instance for `RawTermSubst`.

* `liftForRaw_var_zero` — `(sigma.lift) ⟨0, _⟩ = RawTerm.var
  ⟨0, Nat.zero_lt_succ _⟩` by the var-zero arm of
  `RawTermSubst.lift`; `varToRawTerm` returns it directly.  Holds
  by `rfl`.

* `liftForRaw_var_succ` — `(sigma.lift) ⟨k+1, h⟩
    = (sigma ⟨k, _⟩).rename RawRenaming.weaken`
  by the var-succ arm of `RawTermSubst.lift`; this is the definition
  of `RawTerm.weaken (sigma ⟨k, _⟩)`, which in turn equals
  `RawTerm.weaken (varToRawTerm sigma ⟨k, _⟩)` since
  `varToRawTerm sigma pos = sigma pos`.  Holds by `rfl`. -/
instance : ActsOnRawTermVarLifts RawTermSubst where
  liftForRaw_var_zero := fun _ => rfl
  liftForRaw_var_succ := fun _ _ => rfl

/-! ## Smoke equivalences with existing `RawTerm.rename` / `RawTerm.subst`.

The `RawTerm.act` engine over `RawRenaming` should produce the same
result as the existing `RawTerm.rename`; over `RawTermSubst`, the
same as `RawTerm.subst`.  The full equivalence theorems (~56-case
structural inductions) are deferred to the Z4.B redirect milestone.
For Z4.A we ship the per-ctor `rfl`-bodied smoke theorems
demonstrating that the engine reduces correctly at leaf, recursive,
binder, and var positions on each Container. -/

/-- Smoke: identity-of-act on `RawTerm.unit` under a renaming. -/
theorem RawTerm.act_rawRenaming_unit_smoke
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope) :
    (RawTerm.unit (scope := sourceScope)).act someRenaming = .unit := rfl

/-- Smoke: var-arm under a renaming wraps the renamed Fin. -/
theorem RawTerm.act_rawRenaming_var_smoke
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (position : Fin sourceScope) :
    (RawTerm.var position).act someRenaming = RawTerm.var (someRenaming position) := rfl

/-- Smoke: app-arm under a renaming recurses both subterms. -/
theorem RawTerm.act_rawRenaming_app_smoke
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (functionTerm argumentTerm : RawTerm sourceScope) :
    (RawTerm.app functionTerm argumentTerm).act someRenaming =
      RawTerm.app (functionTerm.act someRenaming) (argumentTerm.act someRenaming) := rfl

/-- Smoke: lam-arm under a renaming uses `Action.liftForRaw`. -/
theorem RawTerm.act_rawRenaming_lam_smoke
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (body : RawTerm (sourceScope + 1)) :
    (RawTerm.lam body).act someRenaming =
      RawTerm.lam (body.act (Action.liftForRaw someRenaming)) := rfl

/-- Smoke: pathLam-arm under a renaming uses `Action.liftForRaw`. -/
theorem RawTerm.act_rawRenaming_pathLam_smoke
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (body : RawTerm (sourceScope + 1)) :
    (RawTerm.pathLam body).act someRenaming =
      RawTerm.pathLam (body.act (Action.liftForRaw someRenaming)) := rfl

/-- Smoke: universeCode is scope-polymorphic and unchanged by act. -/
theorem RawTerm.act_rawRenaming_universeCode_smoke
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (innerLevel : Nat) :
    (RawTerm.universeCode (scope := sourceScope) innerLevel).act someRenaming =
      RawTerm.universeCode innerLevel := rfl

/-- Smoke: identity-of-act on `RawTerm.unit` under a substitution. -/
theorem RawTerm.act_rawTermSubst_unit_smoke
    {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope) :
    (RawTerm.unit (scope := sourceScope)).act sigma = .unit := rfl

/-- Smoke: var-arm under a substitution returns the substituent. -/
theorem RawTerm.act_rawTermSubst_var_smoke
    {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope)
    (position : Fin sourceScope) :
    (RawTerm.var position).act sigma = sigma position := rfl

/-- Smoke: app-arm under a substitution recurses both subterms. -/
theorem RawTerm.act_rawTermSubst_app_smoke
    {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope)
    (functionTerm argumentTerm : RawTerm sourceScope) :
    (RawTerm.app functionTerm argumentTerm).act sigma =
      RawTerm.app (functionTerm.act sigma) (argumentTerm.act sigma) := rfl

/-- Smoke: lam-arm under a substitution uses `Action.liftForRaw`. -/
theorem RawTerm.act_rawTermSubst_lam_smoke
    {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope)
    (body : RawTerm (sourceScope + 1)) :
    (RawTerm.lam body).act sigma =
      RawTerm.lam (body.act (Action.liftForRaw sigma)) := rfl

/-- Smoke: pathLam-arm under a substitution uses `Action.liftForRaw`. -/
theorem RawTerm.act_rawTermSubst_pathLam_smoke
    {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope)
    (body : RawTerm (sourceScope + 1)) :
    (RawTerm.pathLam body).act sigma =
      RawTerm.pathLam (body.act (Action.liftForRaw sigma)) := rfl

/-- Smoke: universeCode is scope-polymorphic under substitution too. -/
theorem RawTerm.act_rawTermSubst_universeCode_smoke
    {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope)
    (innerLevel : Nat) :
    (RawTerm.universeCode (scope := sourceScope) innerLevel).act sigma =
      RawTerm.universeCode innerLevel := rfl

/-- Smoke: identity-action on `RawTerm.unit` reduces to the same term
under `RawRenaming.identity`. -/
theorem RawTerm.act_identity_rawRenaming_unit_smoke {scope : Nat} :
    (RawTerm.unit (scope := scope)).act (RawRenaming.identity (scope := scope)) =
      RawTerm.unit := rfl

/-- Smoke: identity-action on `RawTerm.unit` reduces to the same term
under `RawTermSubst.identity`. -/
theorem RawTerm.act_identity_rawTermSubst_unit_smoke {scope : Nat} :
    (RawTerm.unit (scope := scope)).act (RawTermSubst.identity (scope := scope)) =
      RawTerm.unit := rfl

/-- Smoke: identity-action on `RawTerm.var` reduces to the same
variable under `RawRenaming.identity`. -/
theorem RawTerm.act_identity_rawRenaming_var_smoke
    {scope : Nat} (position : Fin scope) :
    (RawTerm.var position).act (RawRenaming.identity (scope := scope)) =
      RawTerm.var position := rfl

/-- Smoke: identity-action on `RawTerm.var` reduces to the same
variable under `RawTermSubst.identity`. -/
theorem RawTerm.act_identity_rawTermSubst_var_smoke
    {scope : Nat} (position : Fin scope) :
    (RawTerm.var position).act (RawTermSubst.identity (scope := scope)) =
      RawTerm.var position := rfl


end LeanFX2
