import FX1Poly.Foundation.RawSubst.RenameDefs
import FX1Poly.Foundation.Action

/-! # FX1Poly.Foundation.RawSubst.ActionInstances — Action instance for RawRenaming

The **`Action RawRenaming`** instance.  `FX1Poly.Core.LiftsRaw`
projects `Action.liftForRaw` to satisfy `LiftsRaw RawRenaming`, which
is what `FX1Poly.Core.Fold` requires for the rename-style traversal
of `.mkGen` cells.

PolyCell's `RawTerm` defines its own `ActsOnRawTermVar` over
`FX1Poly.Core.RawTerm` in `FX1Poly.Core.RawTermSubstDefs`, with its
own subst Container there — not here.

## Root status

Definitional `rfl`-bodied instance; strict zero-axiom. -/

namespace FX1Poly.Foundation

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

end FX1Poly.Foundation
