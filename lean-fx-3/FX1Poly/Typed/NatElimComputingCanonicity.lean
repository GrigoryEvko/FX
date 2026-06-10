import FX1Poly.Typed.ClosedNatCanonicity
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/NatElimComputingCanonicity
    — the RECURSIVE eliminator-computing canonicity (the nat analogue of `boolElimValueCanonicity`)

`boolElimValueCanonicity` (#1070/#1138 first brick) shipped the FIRST eliminator-computing canonicity: a closed
`boolElim b t e : Bool` with data-VALUE branches computes by a single ι-step to a bool value.  That case is
NON-recursive — `boolElim`'s branches are themselves values, so one ι-step lands the answer.

`natElim` is the genuinely RECURSIVE eliminator, and it carries the difficulty the bool case sidesteps: its
successor ι-rule

    natElim (natSucc n) z s  ↝  app (app s n) (natElim n z s)

(1) reintroduces a `natElim` subterm (the recursive call must ALSO compute), and (2) feeds the result to the
successor branch `s`, which is a FUNCTION (`Nat → C → C`), not a value — so its application must β-reduce.
"Data-value branches" do not transfer.  This file closes that recursive case.

## What this ships

  * **`natElimCell`** — the `gen_natElim` cell `natElim(scrutinee, zeroBranch, succBranch)`.
  * **`natElimComputesToNumeral` (★)** — the abstract recursive computing canonicity, by induction on the
    scrutinee's `IsNatNumeral` structure.  Zero case: `iotaNatElimZero` projects the zero-branch.  Successor
    case: `iotaNatElimSucc` fires, the IH reduces the inner `natElim n z s` to a numeral `r`
    (`StepStar.appArgument` lifts that reduction through the application's argument position), and then the
    step's own computational obligation `stepProduces` finishes `app (app s n) r` to a numeral.  The
    `stepProduces` hypothesis — "the successor branch applied to a numeral predecessor and a numeral recursive
    result reduces to a numeral" — IS the honest computational content of a recursive eliminator's function
    branch (the bool case had no analogue because its branches were values).
  * **`constNatZeroStep` / `constNatZeroStepProduces` / `natElimConstZeroComputesToNumeral`** — a concrete
    non-vacuous instance: the constant step `λ_. λ_. natZero` collapses every numeral fold to `natZero`.
    Discharges `stepProduces` by two β-steps (the binders drop the closed nullary body — `subst0` computes
    definitionally), then instantiates the abstract theorem: `natElim(n, natZero, λλnatZero) ↝* natZero` for
    every closed numeral `n`.
  * **`copyNatStep` / `copyNatStepProduces` / `natElimCopyComputesToNumeral`** — the genuinely-recursive
    instance: the copy step `λ_. λr. natSucc r` USES the recursive result `r`, so `natElim(n, natZero, copyStep)`
    rebuilds the numeral.  Discharges `stepProduces` to `natSucc r` (the `subst0` computes the de Bruijn index
    through the binder definitionally), so the fold genuinely threads the IH result rather than discarding it.
  * **`natElimCopyComputesToNumeral.two`** — a fully-concrete smoke: `natElim(2, natZero, copyStep) ↝* <numeral>`.

## What this is and what remains (honest)

This is the typed-engine RECURSIVE eliminator-computing canonicity — the recursive heart of #1138.  The
abstract theorem captures exactly the recursive structure (IH + ι + the function branch's β-computation); the
two concrete instances prove it non-vacuous, one discarding and one USING the recursive result.  The remaining
integration is the full standalone typed `HasTypeDescNatElimValue` judgment whose successor branch is
grown-typed at the function type `Nat → C → C` (the parallel of `HasTypeDescBoolElimValue`), feeding its grown
typing into `stepProduces` unconditionally — the GTL table-residency follow-on (#832/#1138).  Here the step's
value-production is supplied explicitly (abstract) and discharged for two concrete steps.

## Zero-axiom verification

`natElimComputesToNumeral` is a two-arm `induction` on `IsNatNumeral` composing `StepStar.single` ι-steps,
`StepStar.appArgument` congruence, and `StepStar.trans_compose`.  The concrete instances discharge their
`stepProduces` by `Step.beta` (with `subst0` computing definitionally on closed bodies) plus `StepStar.appFunction`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The natural-number eliminator cell `natElim(scrutinee, zeroBranch, succBranch)` — `gen_natElim` (arity 3,
`binderShifts = [0, 0, 0]`, all three children at the ambient scope). -/
def natElimCell {scope : Nat} (scrutinee zeroBranch succBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_natElim ()
    (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))

/-- **★ Recursive eliminator-computing canonicity.**  A closed `natElim(n, z, s)` whose zero-branch `z` is a
numeral and whose successor branch `s` produces a numeral when applied to a numeral predecessor and a numeral
recursive result (`stepProduces`) computes (`↝*`) to a numeral, for every closed numeral scrutinee `n`.

Induction on `n`'s `IsNatNumeral`:

  * **zero** — `natElim(natZero, z, s) ↝ z` (`Step.iotaNatElimZero`), and `z` is a numeral.
  * **succ p** — `natElim(natSucc p, z, s) ↝ app (app s p) (natElim p z s)` (`Step.iotaNatElimSucc`).  The IH
    gives `natElim p z s ↝* r` with `r` a numeral; `StepStar.appArgument` lifts that through the outer
    application's argument position to reach `app (app s p) r`; and `stepProduces p r` finishes to a numeral.

The successor branch's `stepProduces` obligation is the genuine recursive-eliminator content: unlike the bool
eliminator (value branches, one ι-step), the recursive step branch is a function whose application must itself
compute. -/
theorem natElimComputesToNumeral {zeroBranch succBranch : RawTerm 0}
    (zeroBranchNumeral : IsNatNumeral zeroBranch)
    (stepProduces : ∀ (predecessor recResult : RawTerm 0),
        IsNatNumeral predecessor → IsNatNumeral recResult →
        ∃ out : RawTerm 0,
          StepStar (appCell (appCell succBranch predecessor) recResult) out ∧ IsNatNumeral out)
    {scrutinee : RawTerm 0} (scrutineeNumeral : IsNatNumeral scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (natElimCell scrutinee zeroBranch succBranch) out ∧ IsNatNumeral out := by
  induction scrutineeNumeral with
  | zero =>
      exact ⟨zeroBranch, StepStar.single Step.iotaNatElimZero, zeroBranchNumeral⟩
  | @succ predecessor _predNumeral ih =>
      obtain ⟨recResult, recChain, recNumeral⟩ := ih
      obtain ⟨out, stepChain, outNumeral⟩ := stepProduces predecessor recResult _predNumeral recNumeral
      refine ⟨out, ?_, outNumeral⟩
      have iotaStep :
          StepStar (natElimCell (natSuccCell predecessor) zeroBranch succBranch)
            (appCell (appCell succBranch predecessor)
              (natElimCell predecessor zeroBranch succBranch)) :=
        StepStar.single Step.iotaNatElimSucc
      have congStep :
          StepStar (appCell (appCell succBranch predecessor)
              (natElimCell predecessor zeroBranch succBranch))
            (appCell (appCell succBranch predecessor) recResult) :=
        StepStar.appArgument (appCell succBranch predecessor) recChain
      exact StepStar.trans_compose iotaStep (StepStar.trans_compose congStep stepChain)

/-! ## Concrete instance 1: the constant-zero fold (discards the recursive result) -/

/-- The constant-zero successor step `λ_. λ_. natZero` — ignores both the predecessor and the recursive
result, collapsing every fold to `natZero`. -/
def constNatZeroStep : RawTerm 0 := lamCell natZeroCell (lamCell natZeroCell (natZeroCell : RawTerm 2))

/-- **`constNatZeroStep` produces `natZero`.**  Applied to any predecessor and recursive result, the two β-steps
drop both binders (the body `natZero` is a closed nullary cell, so `subst0` computes definitionally) and land
`natZero`, a numeral.  Discharges the `stepProduces` obligation for the constant-zero fold. -/
theorem constNatZeroStepProduces (predecessor recResult : RawTerm 0)
    (_predecessorNumeral : IsNatNumeral predecessor) (_recResultNumeral : IsNatNumeral recResult) :
    ∃ out : RawTerm 0,
      StepStar (appCell (appCell constNatZeroStep predecessor) recResult) out ∧ IsNatNumeral out := by
  refine ⟨natZeroCell, ?_, IsNatNumeral.zero⟩
  have firstBeta : Step (appCell constNatZeroStep predecessor)
      (lamCell natZeroCell (natZeroCell : RawTerm 1)) :=
    Step.beta
  have secondBeta : Step (appCell (lamCell natZeroCell (natZeroCell : RawTerm 1)) recResult) natZeroCell :=
    Step.beta
  exact StepStar.trans_compose
    (StepStar.appFunction (StepStar.single firstBeta))
    (StepStar.single secondBeta)

/-- **Constant-zero fold canonicity.**  `natElim(n, natZero, λ_.λ_.natZero)` computes to a numeral (in fact
`natZero`) for every closed numeral `n` — the abstract theorem instantiated at `constNatZeroStep`.  Genuinely
recursive (the proof recurses on `n` and the inner `natElim` reduces via the IH), though this particular step
discards the recursive result. -/
theorem natElimConstZeroComputesToNumeral {scrutinee : RawTerm 0} (scrutineeNumeral : IsNatNumeral scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (natElimCell scrutinee natZeroCell constNatZeroStep) out ∧ IsNatNumeral out :=
  natElimComputesToNumeral IsNatNumeral.zero constNatZeroStepProduces scrutineeNumeral

/-! ## Concrete instance 2: the copy fold (USES the recursive result) -/

/-- The copy/successor step `λ_. λr. natSucc r` — `r` (de Bruijn `0`) is the recursive result, rewrapped in a
`natSucc`.  Folding with base `natZero` rebuilds the numeral, so this step genuinely THREADS the recursive
result rather than discarding it. -/
def copyNatStep : RawTerm 0 :=
  lamCell natZeroCell (lamCell natZeroCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 2))))

/-- **`copyNatStep` produces `natSucc recResult`.**  The two β-steps drop the unused predecessor binder and
substitute the recursive result for `r` (the `subst0` computes the de Bruijn index through the binder
definitionally), landing `natSucc recResult` — a numeral whenever `recResult` is.  Discharges `stepProduces`
for the copy fold. -/
theorem copyNatStepProduces (predecessor recResult : RawTerm 0)
    (_predecessorNumeral : IsNatNumeral predecessor) (recResultNumeral : IsNatNumeral recResult) :
    ∃ out : RawTerm 0,
      StepStar (appCell (appCell copyNatStep predecessor) recResult) out ∧ IsNatNumeral out := by
  refine ⟨natSuccCell recResult, ?_, IsNatNumeral.succ recResultNumeral⟩
  have firstBeta : Step (appCell copyNatStep predecessor)
      (lamCell natZeroCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 1)))) :=
    Step.beta
  have secondBeta : Step (appCell (lamCell natZeroCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 1)))) recResult)
      (natSuccCell recResult) :=
    Step.beta
  exact StepStar.trans_compose
    (StepStar.appFunction (StepStar.single firstBeta))
    (StepStar.single secondBeta)

/-- **★ Copy fold canonicity (recursive result USED).**  `natElim(n, natZero, λ_.λr.natSucc r)` computes to a
numeral for every closed numeral `n` — the abstract theorem instantiated at `copyNatStep`.  Unlike the constant
fold, this step rebuilds the numeral from the recursive result, so it exercises the full recursive-threading
machinery: the inner `natElim` must reduce to a numeral via the IH BEFORE the successor branch can wrap it. -/
theorem natElimCopyComputesToNumeral {scrutinee : RawTerm 0} (scrutineeNumeral : IsNatNumeral scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (natElimCell scrutinee natZeroCell copyNatStep) out ∧ IsNatNumeral out :=
  natElimComputesToNumeral IsNatNumeral.zero copyNatStepProduces scrutineeNumeral

/-- **Fully-concrete non-vacuity smoke**: `natElim(2, natZero, copyStep)` computes to a numeral — the copy fold
on the closed numeral `2 = succ (succ natZero)`. -/
theorem natElimCopyComputesToNumeral.two :
    ∃ out : RawTerm 0,
      StepStar (natElimCell (natSuccCell (natSuccCell natZeroCell)) natZeroCell copyNatStep) out ∧
      IsNatNumeral out :=
  natElimCopyComputesToNumeral (IsNatNumeral.succ (IsNatNumeral.succ IsNatNumeral.zero))

end FX1Poly.Typed
