import LeanFX.Syntax.Reduction.RawCdLemma

namespace LeanFX.Syntax

/-! ## Raw-level confluence theorems.

The diamond property and confluence at the raw level follow
immediately from the Tait–Martin-Löf complete-development pair:
  * `RawStep.par.cd_dominates : par t (cd t)`  (Phase 4d)
  * `RawStep.par.cd_lemma     : par t t' → par t' (cd t)`  (Phase 4e)

`cd t` serves as the join point of all parallel reductions from `t`. -/

/-- **Diamond property** for parallel reduction at raw level:
two parallel reductions from a common source can be completed to
a common reduct.  Proof: `cd t` is the common reduct;
`par t1 (cd t)` and `par t2 (cd t)` both follow from `cd_lemma`. -/
theorem RawStep.par.diamond {scope : Nat}
    {sourceTerm leftTarget rightTarget : RawTerm scope}
    (leftStep : RawStep.par sourceTerm leftTarget)
    (rightStep : RawStep.par sourceTerm rightTarget) :
    ∃ commonReduct, RawStep.par leftTarget commonReduct ∧
      RawStep.par rightTarget commonReduct :=
  ⟨RawTerm.cd sourceTerm,
   RawStep.par.cd_lemma leftStep,
   RawStep.par.cd_lemma rightStep⟩

/-- Reflexive-transitive closure of `RawStep.par`.  Used to state
multi-step confluence (Church-Rosser). -/
inductive RawStep.parStar : {scope : Nat} →
    RawTerm scope → RawTerm scope → Prop
  | refl : ∀ {scope : Nat} (term : RawTerm scope),
      RawStep.parStar term term
  | trans :
      ∀ {scope : Nat} {firstTerm secondTerm thirdTerm : RawTerm scope},
      RawStep.par firstTerm secondTerm →
      RawStep.parStar secondTerm thirdTerm →
      RawStep.parStar firstTerm thirdTerm

/-- Single parallel-step lifts to the reflexive-transitive closure. -/
theorem RawStep.par.toStar {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (parallelStep : RawStep.par sourceTerm targetTerm) :
    RawStep.parStar sourceTerm targetTerm :=
  RawStep.parStar.trans parallelStep (RawStep.parStar.refl _)

/-- Append a parallel step at the end of a `parStar` chain. -/
theorem RawStep.parStar.snoc {scope : Nat}
    {firstTerm secondTerm thirdTerm : RawTerm scope}
    (chain : RawStep.parStar firstTerm secondTerm)
    (parallelStep : RawStep.par secondTerm thirdTerm) :
    RawStep.parStar firstTerm thirdTerm := by
  induction chain with
  | refl _ => exact parallelStep.toStar
  | trans firstStep restChain restIH =>
      exact RawStep.parStar.trans firstStep (restIH parallelStep)

/-- Concatenate two `parStar` chains. -/
theorem RawStep.parStar.append {scope : Nat}
    {firstTerm secondTerm thirdTerm : RawTerm scope}
    (firstChain : RawStep.parStar firstTerm secondTerm)
    (secondChain : RawStep.parStar secondTerm thirdTerm) :
    RawStep.parStar firstTerm thirdTerm := by
  induction firstChain with
  | refl _ => exact secondChain
  | trans firstStep restChain restIH =>
      exact RawStep.parStar.trans firstStep (restIH secondChain)

/-- **Strip lemma** for parallel reduction: if `t` single-step
parallel-reduces to `u` and multi-step parallel-reduces to `v`,
there exists a common reduct `w` with `u` multi-stepping to `w`
and `v` single-stepping to `w`.  Proof by induction on the
multi-step chain, using diamond at each step. -/
theorem RawStep.par.strip {scope : Nat}
    {sourceTerm leftTarget rightTarget : RawTerm scope}
    (leftStep : RawStep.par sourceTerm leftTarget)
    (rightChain : RawStep.parStar sourceTerm rightTarget) :
    ∃ commonReduct, RawStep.parStar leftTarget commonReduct ∧
      RawStep.par rightTarget commonReduct := by
  induction rightChain generalizing leftTarget with
  | refl _ =>
      exact ⟨leftTarget, RawStep.parStar.refl _, leftStep⟩
  | trans firstStep restChain restIH =>
      obtain ⟨intermediateReduct, leftToInter, firstToInter⟩ :=
        RawStep.par.diamond leftStep firstStep
      obtain ⟨commonReduct, interToCommon, rightToCommon⟩ :=
        restIH firstToInter
      exact ⟨commonReduct,
        RawStep.parStar.trans leftToInter interToCommon,
        rightToCommon⟩

/-- **Confluence (Church-Rosser)** for parallel reduction's
reflexive-transitive closure.  Two multi-step parallel reductions
from a common source can be completed to a common reduct. -/
theorem RawStep.parStar.confluence {scope : Nat}
    {sourceTerm leftTarget rightTarget : RawTerm scope}
    (leftChain : RawStep.parStar sourceTerm leftTarget)
    (rightChain : RawStep.parStar sourceTerm rightTarget) :
    ∃ commonReduct, RawStep.parStar leftTarget commonReduct ∧
      RawStep.parStar rightTarget commonReduct := by
  induction leftChain generalizing rightTarget with
  | refl _ => exact ⟨rightTarget, rightChain, RawStep.parStar.refl _⟩
  | trans firstStep restChain restIH =>
      obtain ⟨intermediateReduct, firstStepToInter, rightToInter⟩ :=
        RawStep.par.strip firstStep rightChain
      obtain ⟨commonReduct, restToCommon, interToCommon⟩ :=
        restIH firstStepToInter
      exact ⟨commonReduct, restToCommon,
        RawStep.parStar.trans rightToInter interToCommon⟩

end LeanFX.Syntax
