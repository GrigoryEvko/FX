import FX1Poly.Typed.ClosedNatCanonicity
import FX1Poly.Core.ListCanonicalFormsCandidate
import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.IotaHeadStep
import FX1Poly.Core.HeadStep

/-! # FX1Poly/Typed/ListElimComputingCanonicity
    — the RECURSIVE list eliminator-computing canonicity (completes the recursive-eliminator family)

`NatElimComputingCanonicity` shipped the recursive natElim-computing canonicity.  `listElim` is the OTHER
recursive eliminator, and it carries the same recursive difficulty with MORE structure: its cons ι-rule

    listElim (listCons head tail) nil cons
      ↝  app (app (app cons head) tail) (listElim tail nil cons)

is a TRIPLE-nested app (the successor branch `cons` is a 3-argument curried function `Elt → List → C → C`),
and it reintroduces a `listElim` subterm (the recursive call over the `tail`).  This file completes the
recursive-eliminator computing-canonicity family (nat + list).

## What this ships

  * `listElimCell` — the `gen_listElim` cell in the Phase-Z motive shape (arity 4, `binderShifts =
    [1, 0, 0, 0]`), author order `listElim(motive, scrutinee, nilBranch, consBranch)` emitting the spine
    `(motive, nilBranch, consBranch, scrutinee)`.
  * **`listElimComputesToValue` (★)** — the abstract recursive computing canonicity, general over the result
    predicate `isResultValue`, by induction on the scrutinee's `IsListValue` structure.  Nil case:
    `iotaListElimNil` projects the nil-branch.  Cons case: `iotaListElimCons` fires, the IH reduces the inner
    `listElim tail nil cons` to a value `r` (`StepStar.appArgument` lifts that through the outer application's
    argument position — the recursive call sits in the OUTER app's argument), then the step's `stepProduces`
    obligation finishes `app (app (app cons head) tail) r`.  The `stepProduces` hypothesis — "the cons branch
    applied to a head, a tail, and a value recursive result reduces to a value" — IS the recursive eliminator's
    function-branch computational content (the bool case had no analogue; its branches were values).
  * **`constNatZeroStep3` / `listElimConstZeroComputesToNumeral`** — the constant fold `λ_.λ_.λ_. natZero`
    collapses every list fold to `natZero` (three β-steps, `subst0` computes definitionally on the closed body).
  * **`lengthNatStep` / `listElimLengthComputesToNumeral` (★)** — the genuinely-recursive instance: the LENGTH
    step `λ_.λ_.λr. natSucc r` discards the head and tail but USES the recursive result `r`, so the fold counts
    the list — `listElim(list, natZero, lengthStep)` computes the list's LENGTH as a numeral.  This exercises
    the full recursive-threading machinery: the inner `listElim` must reduce to a numeral via the IH before the
    cons branch can wrap it in a successor.
  * **`listElimLengthComputesToNumeral.two`** — a fully-concrete smoke: the length of a 2-element list computes
    to a numeral (in fact `2`).

## What this is and what remains (honest)

This completes the typed-engine RECURSIVE eliminator-computing canonicity for BOTH recursive eliminators (nat,
list).  The remaining integration is the full standalone typed eliminator judgments whose recursive branch is
grown-typed at the curried function type, feeding the grown typing into `stepProduces` unconditionally (the GTL
table-residency / combined-engine follow-on, #832/#1138).  Here the step's value-production is supplied
explicitly (abstract) and discharged for the constant and length folds.

## Zero-axiom verification

`listElimComputesToValue` is a two-arm `induction` on `IsListValue` composing `StepStar.single` ι-steps,
`StepStar.appArgument` congruence (function fixed = the 2-deep app `app (app cons head) tail`), and
`StepStar.trans_compose`.  The concrete instances discharge `stepProduces` by three `Step.beta` steps (with
`subst0` computing definitionally on closed bodies) plus the double `StepStar.appFunction` reaching past the
triple-nested app's two function layers.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ Recursive list-eliminator computing canonicity.**  A closed `listElim(s, nil, cons)` whose nil-branch
satisfies the result predicate `isResultValue` and whose cons branch produces an `isResultValue` from a head, a
tail, and an `isResultValue` recursive result (`stepProduces`) computes (`↝*`) to an `isResultValue`, for every
closed list value `s`.

Induction on `s`'s `IsListValue`:

  * **nil** — `listElim(nil, nil, cons) ↝ nilBranch` (`IotaHeadStep.iotaListElimNil.toStep`), an `isResultValue`.
  * **cons head tail** — `listElim(cons head tail, nil, cons) ↝ app (app (app cons head) tail) (listElim tail
    nil cons)` (`IotaHeadStep.iotaListElimCons.toStep`).  The IH gives `listElim tail nil cons ↝* r` with `isResultValue r`;
    `StepStar.appArgument` lifts that reduction through the outer application's argument position to reach
    `app (app (app cons head) tail) r`; `stepProduces head tail r` finishes.

The cons branch's `stepProduces` obligation is the recursive eliminator's genuine content: its 3-argument
curried function branch must compute when applied. -/
theorem listElimComputesToValue {isResultValue : RawTerm 0 → Prop}
    {motive : RawTerm 1} {nilBranch consBranch : RawTerm 0}
    (nilBranchValue : isResultValue nilBranch)
    (stepProduces : ∀ (headVal tailVal recResult : RawTerm 0),
        isResultValue recResult →
        ∃ out : RawTerm 0,
          StepStar (appCell (appCell (appCell consBranch headVal) tailVal) recResult) out ∧
          isResultValue out)
    {scrutinee : RawTerm 0} (scrutineeValue : IsListValue scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (listElimCell motive scrutinee nilBranch consBranch) out ∧ isResultValue out := by
  induction scrutineeValue with
  | nil => exact ⟨nilBranch, StepStar.single IotaHeadStep.iotaListElimNil.toStep, nilBranchValue⟩
  | @cons headVal tailVal _headNormal _tailValue ih =>
      obtain ⟨recResult, recChain, recValue⟩ := ih
      obtain ⟨out, stepChain, outValue⟩ := stepProduces headVal tailVal recResult recValue
      refine ⟨out, ?_, outValue⟩
      -- the cons-ι reduct THREADS the same motive into the recursive call (the listElim wrinkle:
      -- cons-ι is not motive-discarding).
      have iotaStep :
          StepStar (listElimCell motive (listConsCell headVal tailVal) nilBranch consBranch)
            (appCell (appCell (appCell consBranch headVal) tailVal)
              (listElimCell motive tailVal nilBranch consBranch)) :=
        StepStar.single IotaHeadStep.iotaListElimCons.toStep
      have congStep :
          StepStar (appCell (appCell (appCell consBranch headVal) tailVal)
              (listElimCell motive tailVal nilBranch consBranch))
            (appCell (appCell (appCell consBranch headVal) tailVal) recResult) :=
        StepStar.appArgument (appCell (appCell consBranch headVal) tailVal) recChain
      exact StepStar.trans_compose iotaStep (StepStar.trans_compose congStep stepChain)

/-! ## Concrete instance 1: the constant-zero fold (discards head, tail, and recursive result) -/

/-- The constant-zero cons step `λ_. λ_. λ_. natZero` — ignores the head, the tail, and the recursive result. -/
def constNatZeroStep3 : RawTerm 0 :=
  lamCell natZeroCell (lamCell natZeroCell (lamCell natZeroCell (natZeroCell : RawTerm 3)))

/-- **`constNatZeroStep3` produces `natZero`.**  Applied to any head, tail, and recursive result, the three
β-steps drop all three binders (the body `natZero` is closed nullary, `subst0` computes definitionally). -/
theorem constNatZeroStep3Produces (headVal tailVal recResult : RawTerm 0)
    (_recResultNumeral : IsNatNumeral recResult) :
    ∃ out : RawTerm 0,
      StepStar (appCell (appCell (appCell constNatZeroStep3 headVal) tailVal) recResult) out ∧
      IsNatNumeral out := by
  refine ⟨natZeroCell, ?_, IsNatNumeral.zero⟩
  have firstBeta : Step (appCell constNatZeroStep3 headVal)
      (lamCell natZeroCell (lamCell natZeroCell (natZeroCell : RawTerm 2))) := HeadStep.beta.toStep
  have secondBeta : Step (appCell (lamCell natZeroCell (lamCell natZeroCell (natZeroCell : RawTerm 2))) tailVal)
      (lamCell natZeroCell (natZeroCell : RawTerm 1)) := HeadStep.beta.toStep
  have thirdBeta : Step (appCell (lamCell natZeroCell (natZeroCell : RawTerm 1)) recResult) natZeroCell := HeadStep.beta.toStep
  exact StepStar.trans_compose
    (StepStar.appFunction (StepStar.appFunction (StepStar.single firstBeta)))
    (StepStar.trans_compose
      (StepStar.appFunction (StepStar.single secondBeta))
      (StepStar.single thirdBeta))

/-- **Constant-zero list fold canonicity.**  `listElim(s, natZero, λ_.λ_.λ_.natZero)` computes to a numeral (in
fact `natZero`) for every closed list value `s` — the abstract theorem at `constNatZeroStep3`.  Genuinely
recursive (the proof recurses on `s`, the inner `listElim` reduces via the IH), though this step discards the
recursive result. -/
theorem listElimConstZeroComputesToNumeral {motive : RawTerm 1} {scrutinee : RawTerm 0}
    (scrutineeValue : IsListValue scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (listElimCell motive scrutinee natZeroCell constNatZeroStep3) out ∧ IsNatNumeral out :=
  listElimComputesToValue (isResultValue := IsNatNumeral)
    IsNatNumeral.zero constNatZeroStep3Produces scrutineeValue

/-! ## Concrete instance 2: the length fold (USES the recursive result) -/

/-- The LENGTH cons step `λ_. λ_. λr. natSucc r` — discards the head and tail but rewraps the recursive result
`r` (de Bruijn `0`) in a `natSucc`.  Folding with base `natZero` counts the list, so this step genuinely
THREADS the recursive result. -/
def lengthNatStep : RawTerm 0 :=
  lamCell natZeroCell (lamCell natZeroCell (lamCell natZeroCell
    (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 3)))))

/-- **`lengthNatStep` produces `natSucc recResult`.**  The three β-steps drop the unused head and tail binders
and substitute the recursive result for `r` (`subst0` computes the de Bruijn index through the binders
definitionally), landing `natSucc recResult` — a numeral whenever `recResult` is. -/
theorem lengthNatStepProduces (headVal tailVal recResult : RawTerm 0)
    (recResultNumeral : IsNatNumeral recResult) :
    ∃ out : RawTerm 0,
      StepStar (appCell (appCell (appCell lengthNatStep headVal) tailVal) recResult) out ∧
      IsNatNumeral out := by
  refine ⟨natSuccCell recResult, ?_, IsNatNumeral.succ recResultNumeral⟩
  have firstBeta : Step (appCell lengthNatStep headVal)
      (lamCell natZeroCell (lamCell natZeroCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 2))))) := HeadStep.beta.toStep
  have secondBeta : Step (appCell (lamCell natZeroCell (lamCell natZeroCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 2))))) tailVal)
      (lamCell natZeroCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 1)))) := HeadStep.beta.toStep
  have thirdBeta : Step (appCell (lamCell natZeroCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 1)))) recResult)
      (natSuccCell recResult) := HeadStep.beta.toStep
  exact StepStar.trans_compose
    (StepStar.appFunction (StepStar.appFunction (StepStar.single firstBeta)))
    (StepStar.trans_compose
      (StepStar.appFunction (StepStar.single secondBeta))
      (StepStar.single thirdBeta))

/-- **★ Length fold canonicity (recursive result USED).**  `listElim(s, natZero, λ_.λ_.λr.natSucc r)` computes
the LENGTH of the closed list value `s` as a numeral.  Unlike the constant fold, the length step counts via the
recursive result, so it exercises the full recursive-threading machinery: the inner `listElim` over the tail
must reduce to a numeral via the IH BEFORE the cons branch can wrap it in a successor. -/
theorem listElimLengthComputesToNumeral {motive : RawTerm 1} {scrutinee : RawTerm 0}
    (scrutineeValue : IsListValue scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (listElimCell motive scrutinee natZeroCell lengthNatStep) out ∧ IsNatNumeral out :=
  listElimComputesToValue (isResultValue := IsNatNumeral)
    IsNatNumeral.zero lengthNatStepProduces scrutineeValue

/-- **Fully-concrete non-vacuity smoke**: the length fold over the 2-element list `[natZero, natZero]` computes
to a numeral — `listElim(cons natZero (cons natZero nil), natZero, lengthStep)`.  The scrutinee is a closed
`IsListValue` (both elements are normal), so the fold counts to `2`. -/
theorem listElimLengthComputesToNumeral.two :
    ∃ out : RawTerm 0,
      StepStar
        (listElimCell (variableCell (⟨0, by decide⟩ : Fin 1))
          (listConsCell natZeroCell (listConsCell natZeroCell listNilCell))
          natZeroCell lengthNatStep) out ∧
      IsNatNumeral out :=
  listElimLengthComputesToNumeral
    (motive := variableCell (⟨0, by decide⟩ : Fin 1))
    (IsListValue.cons rfl (IsListValue.cons rfl IsListValue.nil))

end FX1Poly.Typed
