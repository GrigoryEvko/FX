import FX1Poly.Typed.UnboundedGrowthNotStronglyNormalizing
import FX1Poly.Core.RawTermSubst0Commute

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- `λx. g (x x)` — the Curry self-applicator parameterized by `g` (weakened into the binder scope). -/
def curryHalf (g : RawTerm 0) : RawTerm 0 :=
  lamCell (appCell (RawTerm.weaken g)
    (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)) (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))))

/-- `Ω_g = (λx. g (x x)) (λx. g (x x))` — the Curry fixpoint core for `g`.  At `g = id`-ish it is Ω. -/
def curryOmega (g : RawTerm 0) : RawTerm 0 :=
  appCell (curryHalf g) (curryHalf g)

/-- ★ The Curry fixpoint UNFOLDING: `Ω_g` β-reduces in one step to `g (Ω_g)` — so `Ω_g` is a reduction
fixpoint of `g`.  The redex contracts to `subst0 (g (x x)) (λx.g(xx))`; the weakened `g` survives the
substitution (`weaken_subst_singleton`) and the `x x` recopies the abstraction, giving `g (Ω_g)`. -/
theorem curryOmega_step (g : RawTerm 0) : Step (curryOmega g) (appCell g (curryOmega g)) := by
  have betaStep : Step (curryOmega g)
      (RawTerm.subst0 (appCell (RawTerm.weaken g)
        (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
          (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) (curryHalf g)) := Step.beta
  have contractumEq :
      RawTerm.subst0 (appCell (RawTerm.weaken g)
        (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
          (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) (curryHalf g)
        = appCell g (curryOmega g) := by
    show appCell (RawTerm.subst (RawTermSubst.singleton (curryHalf g)) (RawTerm.weaken g)) (curryOmega g)
      = appCell g (curryOmega g)
    rw [RawTerm.weaken_subst_singleton]
  rw [contractumEq] at betaStep
  exact betaStep

/-- The strictly-growing reduction sequence out of `Ω_g`: the `(n+1)`-th term wraps the `n`-th in one more
`g`-application. -/
def curryDivergentSequence (g : RawTerm 0) : Nat → RawTerm 0
  | 0 => curryOmega g
  | k + 1 => appCell g (curryDivergentSequence g k)

/-- Every term in the divergent sequence steps to the next: index `0` is the fixpoint unfolding; index `k+1`
is an argument-congruence step carrying the inductive step. -/
theorem curryDivergentSequence_steps (g : RawTerm 0) :
    ∀ index, Step (curryDivergentSequence g index) (curryDivergentSequence g (index + 1))
  | 0 => curryOmega_step g
  | k + 1 =>
    Step.cong .gen_app ()
      (StepChildren.there (parentScope := 0) (headShift := 0) (restShifts := [0]) g
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [])
          .childNil (curryDivergentSequence_steps g k)))

/-- ★ `Ω_g` is NOT strongly normalizing — for ANY `g` it diverges by unbounded growth (`Ω_g ↝ g Ω_g ↝
g (g Ω_g) ↝ …`).  Every term gives rise to a non-terminating Curry fixpoint, which is exactly why such a
fixpoint operator is untypable in the SN engine (SN-043). -/
theorem curryOmega_notStronglyNormalizing (g : RawTerm 0) :
    ¬ IsStronglyNormalizing (curryOmega g) :=
  notStronglyNormalizing_of_infiniteReduction (curryDivergentSequence g)
    (curryDivergentSequence_steps g)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.curryOmega_step
#print axioms FX1Poly.Typed.curryDivergentSequence_steps
#print axioms FX1Poly.Typed.curryOmega_notStronglyNormalizing
