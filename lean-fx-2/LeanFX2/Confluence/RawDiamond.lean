/-! # RawDiamond — TODO POLYCELL: BODY DISABLED

Body depends on cd_lemma / Conv.canonical_form / parStar.confluence /
RawStep.parStar orchestration deleted in commit c2efaccf (cascade-fake
bulldoze).  Replacement: FXcdLemma / FXConv view defs per polycell.md §5.
Imports are preserved at top so downstream transitive imports still work.
-/

/- TODO POLYCELL: original body preserved as block comment

/-! # Confluence/RawDiamond — diamond + Church-Rosser at the raw level

The diamond property and confluence at the raw level follow
immediately from the Tait–Martin-Löf complete-development pair:

* `RawStep.par.cd_dominates : par t (cd t)`              (Phase 6.A/6.B.2)
* `RawStep.par.cd_lemma     : par t t' → par t' (cd t)`  (Phase 6.B)

`cd t` serves as the join point of all parallel reductions
from `t`.  Strip-lemma + induction over multi-step chains lifts
the diamond from single-step to multi-step parallel reduction.

## Theorems shipped

* `RawStep.par.diamond` — diamond for single-step parallel reduction
* `RawStep.parStar` — reflexive-transitive closure
* `RawStep.par.toStar` / `parStar.snoc` / `parStar.append`
* `RawStep.par.strip` — strip lemma
* `RawStep.parStar.confluence` — Church-Rosser theorem

All proofs zero-axiom under strict policy.
-/

namespace LeanFX2

/-- **Diamond property** for parallel reduction at raw level.
Two parallel reductions from a common source can be completed
to a common reduct: `cd sourceTerm` itself, since both targets
parallel-reduce to it via `cd_lemma`. -/
theorem RawStep.par.diamond {scope : Nat}
    {sourceTerm leftTarget rightTarget : RawTerm scope}
    (leftStep : RawStep.par sourceTerm leftTarget)
    (rightStep : RawStep.par sourceTerm rightTarget) :
    ∃ commonReduct, RawStep.par leftTarget commonReduct ∧
      RawStep.par rightTarget commonReduct :=
  ⟨RawTerm.cd sourceTerm,
   RawStep.par.cd_lemma leftStep,
   RawStep.par.cd_lemma rightStep⟩

/-- Reflexive-transitive closure of `RawStep.par`.  Used to
state multi-step confluence (Church-Rosser). -/
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
theorem RawStep.par.toStar {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
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
  | trans firstStep _ restIH =>
      exact RawStep.parStar.trans firstStep (restIH parallelStep)

/-- Concatenate two `parStar` chains. -/
theorem RawStep.parStar.append {scope : Nat}
    {firstTerm secondTerm thirdTerm : RawTerm scope}
    (firstChain : RawStep.parStar firstTerm secondTerm)
    (secondChain : RawStep.parStar secondTerm thirdTerm) :
    RawStep.parStar firstTerm thirdTerm := by
  induction firstChain with
  | refl _ => exact secondChain
  | trans firstStep _ restIH =>
      exact RawStep.parStar.trans firstStep (restIH secondChain)

/-- **mapStep — the raw cong-rule lifter.**

`RawStep.parStar.mapStep` takes a raw-term transformer whose action
commutes with single `RawStep.par` reduction and lifts it into one
that commutes with multi-step parallel reduction.  Used to collapse
the 4-line refl/trans induction in every `parStar.<ctor>` cong rule
to a 1-line `mapStep` invocation.

The transformer is allowed to change scope (`innerScope` →
`outerScope`).  This covers binder cong rules (e.g. `parStar.lam`
maps `RawTerm (scope + 1)` to `RawTerm scope`) as well as
same-scope cong rules (e.g. `parStar.fst`).

The raw analog of `StepStar.mapStep` in `Reduction/StepStar.lean`.
Per `feedback_lean_mapStep_pattern.md` discipline: this lifter
removes mechanical induction boilerplate from cong rules. -/
theorem RawStep.parStar.mapStep
    {innerScope outerScope : Nat}
    (wrapRaw : RawTerm innerScope → RawTerm outerScope)
    (wrapStep :
      ∀ {innerSource innerTarget : RawTerm innerScope},
        RawStep.par innerSource innerTarget →
        RawStep.par (wrapRaw innerSource) (wrapRaw innerTarget))
    {innerSource innerTarget : RawTerm innerScope}
    (chain : RawStep.parStar innerSource innerTarget) :
    RawStep.parStar (wrapRaw innerSource) (wrapRaw innerTarget) := by
  induction chain with
  | refl term => exact RawStep.parStar.refl (wrapRaw term)
  | trans firstStep _ restIH =>
      exact RawStep.parStar.trans (wrapStep firstStep) restIH

/-- **Strip lemma** for parallel reduction.  If `t` single-step
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
  | trans firstStep _ restIH =>
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
  | trans firstStep _ restIH =>
      obtain ⟨intermediateReduct, firstStepToInter, rightToInter⟩ :=
        RawStep.par.strip firstStep rightChain
      obtain ⟨commonReduct, restToCommon, interToCommon⟩ :=
        restIH firstStepToInter
      exact ⟨commonReduct, restToCommon,
        RawStep.parStar.trans rightToInter interToCommon⟩

end LeanFX2

-/
