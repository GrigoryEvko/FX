import FX1Poly.Typed.DenoteKeyedReducibility

/-! Scratch: the THIRD interface leg on `denoteBelowFamily` — backward closure under a `WeakHeadStep`,
UNCONDITIONAL (vacuous above the bound, `whnfExpand` below it).  Unlike `lowerNeutralInclusion` (an
existence obligation that FAILS on the empty above-bound family), a backward-STEP leg is an implication
whose premise `denoteBelowFamily ... reduct candidate` is `False` above the bound, hence vacuously holds.
This is the leg the eventual member weak-head β-expansion (the denote lambda-arm engine) needs at its
universe arm — and it being unconditional makes that universe case bound-free. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Foundation FX1Poly.Universe
open StepStar

theorem denoteBelowFamily_backwardWeakHeadStep {scope : Nat} (env : Nat → Nat) (level : Nat) (lvl : Nat)
    {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop}
    (member : denoteBelowFamily env level lvl reduct candidate)
    (weakHeadStep : WeakHeadStep typeCode reduct) :
    denoteBelowFamily env level lvl typeCode candidate := by
  by_cases hlt : lvl < level
  · rw [denoteBelowFamily_eq_reducible env level lvl hlt] at member ⊢
    exact ReducibleTypeStepDenote.whnfExpand weakHeadStep member
  · rw [denoteBelowFamily_eq_empty_of_ge env level lvl (Nat.not_lt.mp hlt)] at member
    exact member.elim

end FX1Poly.Typed

#print axioms FX1Poly.Typed.denoteBelowFamily_backwardWeakHeadStep
