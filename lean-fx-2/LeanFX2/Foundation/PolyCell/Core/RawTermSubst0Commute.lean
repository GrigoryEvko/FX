import LeanFX2.Foundation.PolyCell.Core.RawTermSubst0
import LeanFX2.Foundation.PolyCell.Core.RawTermSubstCompose
import LeanFX2.Foundation.PolyCell.Core.RawTermSubstIdentity

/-! # Foundation/PolyCell/Core/RawTermSubst0Commute

Small beta-replay reshaping lemmas for the v2 raw substrate.

The main theorem, `RawTerm.subst0_subst_commute`, is the contractum
reshape needed when a beta step is replayed after an outer
substitution:

`subst sigma (subst0 body arg) =
 subst0 (subst sigma.lift body) (subst sigma arg)`.

This is the v2 counterpart of the legacy raw beta-compatibility
equation, but it is proved from the generic fold-based
`RawTerm.subst_compose` plus pointwise substitution equality.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-- Pre-composing canonical weakening with singleton substitution gives
the identity substitution pointwise. -/
theorem RawTermSubst.weaken_then_singleton_pointwise {scope : Nat}
    (rawArg : RawTerm scope) :
    RawTermSubst.PointwiseEq
      (RawRenaming.thenSubst RawRenaming.weaken
        (RawTermSubst.singleton rawArg))
      RawTermSubst.identity := by
  intro position
  cases position with
  | mk positionValue positionBound =>
      rfl

/-- Substituting a singleton through a weakened raw term cancels the
weakening and returns the original term. -/
theorem RawTerm.weaken_subst_singleton {scope : Nat}
    (sourceTerm rawArg : RawTerm scope) :
    RawTerm.subst (RawTermSubst.singleton rawArg)
      (RawTerm.weaken sourceTerm) = sourceTerm := by
  rw [RawTerm.weaken_eq_rename]
  rw [RawTerm.rename_subst_commute RawRenaming.weaken
    (RawTermSubst.singleton rawArg) sourceTerm]
  rw [RawTerm.subst_pointwise
    (RawTermSubst.weaken_then_singleton_pointwise rawArg) sourceTerm]
  exact RawTerm.subst_identity_apply sourceTerm

/-- Singleton substitution cancels the matching lifted weakening under
`binderDepth` child binders. -/
theorem RawTerm.subst_iterateLiftRaw_singleton_weaken
    {scope binderDepth : Nat}
    (sourceTerm : RawTerm (scope + binderDepth))
    (rawArg : RawTerm scope) :
    RawTerm.subst
        (iterateLiftRaw (RawTermSubst.singleton rawArg) binderDepth)
        (RawTerm.rename
          (iterateLiftRaw RawRenaming.weaken binderDepth) sourceTerm) =
      sourceTerm := by
  rw [RawTerm.rename_subst_commute
    (iterateLiftRaw RawRenaming.weaken binderDepth)
    (iterateLiftRaw (RawTermSubst.singleton rawArg) binderDepth)
    sourceTerm]
  have pulled :
      RawTermSubst.PointwiseEq
        (iterateLiftRaw
          (RawRenaming.thenSubst RawRenaming.weaken
            (RawTermSubst.singleton rawArg)) binderDepth)
        (RawRenaming.thenSubst
          (iterateLiftRaw RawRenaming.weaken binderDepth)
          (iterateLiftRaw (RawTermSubst.singleton rawArg) binderDepth)) :=
    iterateLiftRaw_RawRenaming_thenSubst_pointwise
      RawRenaming.weaken (RawTermSubst.singleton rawArg) binderDepth
  have basePointwise :
      RawTermSubst.PointwiseEq
        (RawRenaming.thenSubst RawRenaming.weaken
          (RawTermSubst.singleton rawArg))
        (RawTermSubst.identity (scope := scope)) :=
    RawTermSubst.weaken_then_singleton_pointwise rawArg
  have liftedBase :
      RawTermSubst.PointwiseEq
        (iterateLiftRaw
          (RawRenaming.thenSubst RawRenaming.weaken
            (RawTermSubst.singleton rawArg)) binderDepth)
        (iterateLiftRaw (RawTermSubst.identity (scope := scope))
          binderDepth) :=
    iterateLiftRaw_RawTermSubst_pointwise basePointwise binderDepth
  have liftedIdentity :
      RawTermSubst.PointwiseEq
        (iterateLiftRaw (RawTermSubst.identity (scope := scope))
          binderDepth)
        (RawTermSubst.identity (scope := scope + binderDepth)) :=
    iterateLiftRaw_identity_pointwise (scope := scope) binderDepth
  rw [RawTerm.subst_pointwise
    (fun position => (pulled position).symm) sourceTerm]
  rw [RawTerm.subst_pointwise liftedBase sourceTerm]
  rw [RawTerm.subst_pointwise liftedIdentity sourceTerm]
  exact RawTerm.subst_identity_apply sourceTerm

/-- Children-spine sibling of
`RawTerm.subst_iterateLiftRaw_singleton_weaken`. -/
theorem RawTermChildren.subst_iterateLiftRaw_singleton_weaken
    {scope binderDepth : Nat} {binderShifts : List Nat}
    (children : RawTermChildren binderShifts (scope + binderDepth))
    (rawArg : RawTerm scope) :
    RawTermChildren.subst
        (iterateLiftRaw (RawTermSubst.singleton rawArg) binderDepth)
        (RawTermChildren.rename
          (iterateLiftRaw RawRenaming.weaken binderDepth) children) =
      children := by
  rw [RawTermChildren.rename_subst_commute
    (iterateLiftRaw RawRenaming.weaken binderDepth)
    (iterateLiftRaw (RawTermSubst.singleton rawArg) binderDepth)
    children]
  have pulled :
      RawTermSubst.PointwiseEq
        (iterateLiftRaw
          (RawRenaming.thenSubst RawRenaming.weaken
            (RawTermSubst.singleton rawArg)) binderDepth)
        (RawRenaming.thenSubst
          (iterateLiftRaw RawRenaming.weaken binderDepth)
          (iterateLiftRaw (RawTermSubst.singleton rawArg) binderDepth)) :=
    iterateLiftRaw_RawRenaming_thenSubst_pointwise
      RawRenaming.weaken (RawTermSubst.singleton rawArg) binderDepth
  have basePointwise :
      RawTermSubst.PointwiseEq
        (RawRenaming.thenSubst RawRenaming.weaken
          (RawTermSubst.singleton rawArg))
        (RawTermSubst.identity (scope := scope)) :=
    RawTermSubst.weaken_then_singleton_pointwise rawArg
  have liftedBase :
      RawTermSubst.PointwiseEq
        (iterateLiftRaw
          (RawRenaming.thenSubst RawRenaming.weaken
            (RawTermSubst.singleton rawArg)) binderDepth)
        (iterateLiftRaw (RawTermSubst.identity (scope := scope))
          binderDepth) :=
    iterateLiftRaw_RawTermSubst_pointwise basePointwise binderDepth
  have liftedIdentity :
      RawTermSubst.PointwiseEq
        (iterateLiftRaw (RawTermSubst.identity (scope := scope))
          binderDepth)
        (RawTermSubst.identity (scope := scope + binderDepth)) :=
    iterateLiftRaw_identity_pointwise (scope := scope) binderDepth
  rw [RawTermChildren.subst_pointwise
    (fun position => (pulled position).symm) children]
  rw [RawTermChildren.subst_pointwise liftedBase children]
  rw [RawTermChildren.subst_pointwise liftedIdentity children]
  exact RawTermChildren.subst_identity_apply children

/-- Substituting a singleton through a weakened raw-term children spine
cancels the weakening and returns the original spine. -/
theorem RawTermChildren.weaken_subst_singleton {scope : Nat}
    {binderShifts : List Nat}
    (children : RawTermChildren binderShifts scope)
    (rawArg : RawTerm scope) :
    RawTermChildren.subst (RawTermSubst.singleton rawArg)
      (RawTermChildren.weaken children) = children := by
  unfold RawTermChildren.weaken
  exact RawTermChildren.subst_iterateLiftRaw_singleton_weaken
    (binderDepth := 0) children rawArg

/-- `subst0` commutes with a following substitution.

This is the beta-contractum reshape used by substitution replay:
after substituting a beta reduct, the result is exactly the beta
reduct of the substituted body and substituted argument. -/
theorem RawTerm.subst0_subst_commute {sourceScope targetScope : Nat}
    (body : RawTerm (sourceScope + 1)) (rawArg : RawTerm sourceScope)
    (sigma : RawTermSubst sourceScope targetScope) :
    RawTerm.subst sigma (RawTerm.subst0 body rawArg) =
      RawTerm.subst0
        (RawTerm.subst (RawTermSubst.lift sigma) body)
        (RawTerm.subst sigma rawArg) := by
  unfold RawTerm.subst0
  rw [RawTerm.subst_compose (RawTermSubst.singleton rawArg) sigma body]
  rw [RawTerm.subst_compose (RawTermSubst.lift sigma)
    (RawTermSubst.singleton (RawTerm.subst sigma rawArg)) body]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound =>
      cases positionValue with
      | zero => rfl
      | succ priorPositionValue =>
          dsimp only [RawTermSubst.compose, RawTermSubst.singleton,
            RawTermSubst.lift]
          exact (RawTerm.weaken_subst_singleton
            (sigma ⟨priorPositionValue,
              Nat.lt_of_succ_lt_succ positionBound⟩)
            (RawTerm.subst sigma rawArg)).symm

end LeanFX2.Foundation.PolyCell.Core
