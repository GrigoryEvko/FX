import FX1Poly.Core.BetaRedexStrongNormalization
import FX1Poly.Typed.DenoteKeyedReducibility

/-! Scratch: universe-candidate member β-expansion (the universe arm of the denote member weak-head
β-expansion / lambda-arm engine). For the denote universe candidate `universeDenotePredicate env lowerAt e`,
the β-redex `app (lam body) arg` is a member given the contractum `subst0 body arg` is a member (+ SN guards
on binder/argument). SN conjunct via `appLam_isStronglyNormalizing_of_contractum`; `∃c, lowerAt(denote e) · c`
conjunct via the (unconditional, for `denoteBelowFamily`) lower backward-weak-head-step leg on `WeakHeadStep.beta`.
Parametric over the leg (instantiated later by `denoteBelowFamily_backwardWeakHeadStep`). -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem universeMemberBetaExpansionAtDenote {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    (levelExpr : LevelExpr)
    (lowerBackwardWeakHeadStep :
      ∀ {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop},
        lowerAt (LevelExpr.denote levelExpr env) reduct candidate → WeakHeadStep typeCode reduct →
        lowerAt (LevelExpr.denote levelExpr env) typeCode candidate)
    {body : RawTerm (scope + 1)} {arg : RawTerm scope}
    (lamStronglyNormalizing :
      IsStronglyNormalizing (.mkGen .gen_lam () (.childCons body .childNil)))
    (argumentStronglyNormalizing : IsStronglyNormalizing arg)
    (contractumMember : universeDenotePredicate env lowerAt levelExpr (RawTerm.subst0 body arg)) :
    universeDenotePredicate env lowerAt levelExpr
      (applicationCell (.mkGen .gen_lam () (.childCons body .childNil)) arg) :=
  ⟨appLam_isStronglyNormalizing_of_contractum lamStronglyNormalizing argumentStronglyNormalizing
      contractumMember.1,
    match contractumMember.2 with
    | ⟨candidate, lowerMember⟩ =>
        ⟨candidate, lowerBackwardWeakHeadStep lowerMember WeakHeadStep.beta⟩⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeMemberBetaExpansionAtDenote
