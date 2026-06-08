import FX1Poly.Typed.CurryFixpointDivergence

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- `λx. f (x x)` at scope 1: f is the outer-bound variable (de Bruijn 1), x the inner (de Bruijn 0). -/
def fixInnerHalf : RawTerm 1 :=
  lamCell (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
    (appCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)) (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))

/-- The Curry fixpoint combinator `fix = λf. (λx. f(xx)) (λx. f(xx))`. -/
def fixCombinator : RawTerm 0 :=
  lamCell (appCell fixInnerHalf fixInnerHalf)

/-- Applying `fix` to `g` β-reduces to `Ω_g`: the body's `f` is replaced by `g`, and the under-binder
substitution `subst0 fixInnerHalf g` computes to `curryHalf g` definitionally. -/
theorem fixCombinator_applied_step (g : RawTerm 0) :
    Step (appCell fixCombinator g) (curryOmega g) :=
  Step.beta

/-- `fix g ↝* g (Ω_g)` in two steps: the instantiation β, then the fixpoint unfolding `Ω_g ↝ g(Ω_g)`. -/
theorem fixCombinator_reducesToUnfolding (g : RawTerm 0) :
    StepStar (appCell fixCombinator g) (appCell g (curryOmega g)) :=
  StepStar.trans (fixCombinator_applied_step g)
    (StepStar.trans (curryOmega_step g) (StepStar.refl _))

/-- ★ THE FIXPOINT PROPERTY: `fix g` is convertible to `g (fix g)`.  Both reduce to the common term
`g (Ω_g)` — `fix g` in two steps, `g (fix g)` in one argument-congruence step — so they are definitionally
equal.  This is the defining equation of a fixpoint combinator: `fix g =_β g (fix g)`. -/
theorem fixCombinator_isFixpoint (g : RawTerm 0) :
    Conv (appCell fixCombinator g) (appCell g (appCell fixCombinator g)) := by
  have rightStep : Step (appCell g (appCell fixCombinator g)) (appCell g (curryOmega g)) :=
    Step.cong .gen_app ()
      (StepChildren.there (parentScope := 0) (headShift := 0) (restShifts := [0]) g
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [])
          .childNil (fixCombinator_applied_step g)))
  exact Conv.trans (Conv.fromStepStar (fixCombinator_reducesToUnfolding g))
    (Conv.sym (Conv.fromStepStar (StepStar.trans rightStep (StepStar.refl _))))

/-- `fix g` is NOT strongly normalizing: it steps to the non-terminating `Ω_g`, so it inherits the
divergence (a reduct of an SN term would be SN). -/
theorem fixCombinator_applied_notStronglyNormalizing (g : RawTerm 0) :
    ¬ IsStronglyNormalizing (appCell fixCombinator g) :=
  fun stronglyNormalizing =>
    curryOmega_notStronglyNormalizing g (stronglyNormalizing.inv (fixCombinator_applied_step g))

end FX1Poly.Typed

#print axioms FX1Poly.Typed.fixCombinator_applied_step
#print axioms FX1Poly.Typed.fixCombinator_reducesToUnfolding
#print axioms FX1Poly.Typed.fixCombinator_isFixpoint
#print axioms FX1Poly.Typed.fixCombinator_applied_notStronglyNormalizing
