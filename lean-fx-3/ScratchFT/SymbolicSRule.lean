import FX1Poly.Typed.CombinatoryCompleteness
import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Core.RawTermRenameSubstCommute
import FX1Poly.Core.RawTermSubstRenameCommute

namespace FX1Poly.Core
open FX1Poly.Foundation

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

theorem subst_lift_singleton_weaken_weaken {scope : Nat}
    (innerArg outerArg : RawTerm scope) :
    RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton outerArg))
        (RawTerm.weaken (RawTerm.weaken innerArg))
      = RawTerm.weaken innerArg := by
  rw [subst_lift_weaken (RawTermSubst.singleton outerArg) (RawTerm.weaken innerArg)]
  rw [RawTerm.weaken_subst_singleton innerArg outerArg]

end FX1Poly.Core

namespace FX1Poly.Typed
open FX1Poly.Core StepStar

-- probe the three reshapes for the symbolic S-rule.
theorem probe_Rsab (a b : RawTerm 0) :
    RawTerm.subst0
        (lamCell (appCell (appCell (RawTerm.weaken (RawTerm.weaken a))
          (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))
          (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))) b
      = sabTerm a b := by
  unfold RawTerm.subst0 sabTerm
  show lamCell (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton b)) _) = _
  rw [show RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton b))
        (RawTerm.weaken (RawTerm.weaken a)) = RawTerm.weaken a from
      subst_lift_singleton_weaken_weaken a b]
  rfl

end FX1Poly.Typed

#print axioms FX1Poly.Core.subst_lift_singleton_weaken_weaken
#print axioms FX1Poly.Typed.probe_Rsab
