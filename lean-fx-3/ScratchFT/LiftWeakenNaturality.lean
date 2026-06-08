import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Core.RawTermRenameSubstCommute
import FX1Poly.Core.RawTermSubstRenameCommute

namespace FX1Poly.Core

open FX1Poly.Foundation

-- The lift-weaken naturality: subst (lift sigma) (weaken t) = weaken (subst sigma t).
theorem subst_lift_weaken {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope) (sourceTerm : RawTerm sourceScope) :
    RawTerm.subst (RawTermSubst.lift sigma) (RawTerm.weaken sourceTerm)
      = RawTerm.weaken (RawTerm.subst sigma sourceTerm) := by
  rw [RawTerm.weaken_eq_rename sourceTerm,
    RawTerm.weaken_eq_rename (RawTerm.subst sigma sourceTerm)]
  rw [RawTerm.rename_subst_commute RawRenaming.weaken (RawTermSubst.lift sigma) sourceTerm]
  rw [RawTerm.subst_rename_commute sigma RawRenaming.weaken sourceTerm]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound => rfl

-- The double-weaken cancellation that blocks the symbolic S-rule / Church-sums.
theorem subst_lift_singleton_weaken_weaken {scope : Nat}
    (innerArg outerArg : RawTerm scope) :
    RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton outerArg))
        (RawTerm.weaken (RawTerm.weaken innerArg))
      = RawTerm.weaken innerArg := by
  rw [subst_lift_weaken (RawTermSubst.singleton outerArg) (RawTerm.weaken innerArg)]
  rw [RawTerm.weaken_subst_singleton innerArg outerArg]

end FX1Poly.Core

#print axioms FX1Poly.Core.subst_lift_weaken
#print axioms FX1Poly.Core.subst_lift_singleton_weaken_weaken
