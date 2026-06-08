import FX1Poly.Typed.DenoteKeyedReducibility

/-! Scratch: discharge the parametric-CR interface legs for `denoteBelowFamily env level`.
forwardStep holds unconditionally (below-family forward-closed at each level); neutralInclusion holds for
lvl < level (below that bound the family is the real relation; at/above it is empty, and neutral-inclusion
of the empty relation is FALSE — the SN-001 degeneracy re-keyed to denote). These are exactly the legs the
parametric ReducibleTypeStepDenote.isReducibilityCandidate consumes at the universe arm's decoded level,
and the piArm will satisfy lvl = denote e < level via denote_lt_lsucc. Probe: all zero-axiom. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Foundation FX1Poly.Universe
open StepStar

/-- Single-step forward closure (denote-keyed), port of ReducibleTypeStep.forwardStep. -/
theorem ReducibleTypeStepDenote.forwardStep {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) (step : Step typeCode reduct) :
    ReducibleTypeStepDenote env lowerAt reduct candidate :=
  ReducibleTypeStepDenote.forwardStepStar reducible (StepStar.single step)

/-- A neutral type is reducible (denote-keyed), port of ReducibleTypeStep.reducibleOfNeutral. -/
theorem ReducibleTypeStepDenote.reducibleOfNeutral {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} (neutral : IsNeutral typeCode) :
    ∃ candidate : RawTerm scope → Prop, ReducibleTypeStepDenote env lowerAt typeCode candidate := by
  refine ⟨IsStronglyNormalizing, ReducibleTypeStepDenote.neutral
    (fun reduct => neutral.noWeakHeadStep reduct) ?_ ?_⟩
  · cases neutral <;> exact fun rootEquation => nomatch rootEquation
  · cases neutral <;> exact fun rootEquation => nomatch rootEquation

/-- The below-family is the EMPTY relation at or above the level. -/
theorem denoteBelowFamily_eq_empty_of_ge {scope : Nat} (env : Nat → Nat) :
    ∀ (level lvl : Nat), level ≤ lvl →
      denoteBelowFamily (scope := scope) env level lvl = (fun _ _ => False) := by
  intro level
  induction level with
  | zero => intro lvl _; rfl
  | succ predLevel _ih =>
      intro lvl hle
      have predLessThan : predLevel < lvl := Nat.lt_of_lt_of_le (Nat.lt_succ_self predLevel) hle
      show (if lvl < predLevel then denoteBelowFamily env predLevel lvl
            else if lvl = predLevel then ReducibleTypeStepDenote env (denoteBelowFamily env predLevel)
            else fun _ _ => False) = fun _ _ => False
      rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt predLessThan)),
        if_neg (Ne.symm (Nat.ne_of_lt predLessThan))]

/-- **Interface leg 1 (unconditional): the below-family is forward-closed under `Step` at every level.**
Below the bound, coherence reduces to the real relation's forward closure; at/above it the family is empty
(vacuous). -/
theorem denoteBelowFamily_forwardStep {scope : Nat} (env : Nat → Nat) (level : Nat) (lvl : Nat)
    {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop}
    (member : denoteBelowFamily env level lvl typeCode candidate) (step : Step typeCode reduct) :
    denoteBelowFamily env level lvl reduct candidate := by
  by_cases hlt : lvl < level
  · rw [denoteBelowFamily_eq_reducible env level lvl hlt] at member ⊢
    exact ReducibleTypeStepDenote.forwardStep member step
  · rw [denoteBelowFamily_eq_empty_of_ge env level lvl (Nat.not_lt.mp hlt)] at member
    exact member.elim

/-- **Interface leg 2 (bounded by `lvl < level`): neutral-inclusion of the below-family.**  Below the
bound, coherence reduces to the real relation, where a neutral type is reducible
(`reducibleOfNeutral`).  At/above the bound the family is empty and this FAILS (a variable is neutral with
no reducts yet the empty relation has no members) — the precise level-bound the `piArm` satisfies via
`denote e < level`. -/
theorem denoteBelowFamily_neutralInclusion_of_lt {scope : Nat} (env : Nat → Nat) (level : Nat) (lvl : Nat)
    (hlt : lvl < level) {typeCode : RawTerm scope} (neutral : IsNeutral typeCode)
    (_reductsReducible : ∀ reduct : RawTerm scope, Step typeCode reduct →
      ∃ candidate : RawTerm scope → Prop, denoteBelowFamily env level lvl reduct candidate) :
    ∃ candidate : RawTerm scope → Prop, denoteBelowFamily env level lvl typeCode candidate := by
  rw [denoteBelowFamily_eq_reducible env level lvl hlt]
  exact ReducibleTypeStepDenote.reducibleOfNeutral neutral

end FX1Poly.Typed

#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.forwardStep
#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.reducibleOfNeutral
#print axioms FX1Poly.Typed.denoteBelowFamily_eq_empty_of_ge
#print axioms FX1Poly.Typed.denoteBelowFamily_forwardStep
#print axioms FX1Poly.Typed.denoteBelowFamily_neutralInclusion_of_lt
