import FX1Poly.Typed.ClosedNumeralSubstInvariant

/-! # FX1Poly/Typed/NatElimFaithfulMul — the native `natElim` recursor FAITHFULLY computes host `Nat.mul` (HON-13)

`NatElimFaithfulArithmetic.natElimAddFaithful` proved the native `gen_natElim` recursor computes host `Nat.add`
(the copy fold).  This file completes HON-13 with the genuinely harder case: host `Nat.mul`.  Multiplication folds
"add `m`" `n` times, so its step branch must ITSELF run a recursor — `mulNatStep m = λ_.λr.natElim(numeralM, r,
copyStep)` embeds the multiplicand numeral and a recursor under two binders.  That embedding is exactly what made
the β-reduction stall: for a SYMBOLIC `m`, the engine must push the step's substitution through the stuck
`natNumeralAt m`, which does not compute by `rfl`.  `ClosedNumeralSubstInvariant.natNumeralAt_subst` (the crack)
fixes the numeral under any substitution, so the β-reduct is rewritten explicitly and the assembly goes through —
reusing `natElimAddFaithful` as the per-step adder.

  * **`copyNatStepAt {scope}`** — the scope-polymorphic copy step (the existing `copyNatStep` is scope-0 only; it
    lives at scope 2 inside `mulNatStep`'s binders); `copyNatStepAt_zero` is the `rfl` bridge to `copyNatStep`.
  * **`mulNatStep m`** — `λ_.λr.natElim(numeralM, r, copyStep)`: folds "add `m`" onto the accumulator `r` (the
    inner recursor adds `m` to `r` via the copy step, base `r`, scrutinee `numeralM`).
  * **`mulStepFires`** — the step's two β-reductions land the inner adder
    `natElim(natNumeralAt m, rec, copyStepAt)` with the embedded numeral fixed by `natNumeralAt_subst` (each
    `Step.beta` produces the raw `subst0 body arg`; the explicit `firstEq`/`secondEq` rewrite it to the target —
    the recipe for any "closed term under binders" β-step, since asserting the pretty reduct directly fails on
    the stuck symbolic numeral).
  * **`natElimMulFaithful` (★ headline)** — `natElim(rawNat n, 0, mulStep m) ↝* rawNat (m·n)` for ALL `m n` —
    the native recursor computes EXACTLY host `Nat.mul`.  Induction on `n`: zero gives `natZero`
    (`iotaNatElimZero`); successor fires `iotaNatElimSucc`, the IH reduces the inner recursor, `mulStepFires`
    lands the adder, and `natElimAddFaithful (m·n) m` finishes to `numeral (m·n + m) = numeral (m·(n+1))`
    (definitional via `Nat.mul_succ`).
  * **`natElimMulFaithful.threeTimesTwo`** — fully-concrete `natElim(2, 0, mulStep 3) ↝* 6`.

With `natElimAddFaithful` (Nat.add) and this (Nat.mul), the native `gen_natElim` truthfully encodes the host
arithmetic recursor — the deepest "the cell computes its named mathematical meaning" of the honesty arc.

## Zero-axiom

`mulStepFires` is two `Step.beta` whose `subst0` reducts are rewritten by `natNumeralAt_subst` (the Fin bounds
use `Nat.succ_pos _`, NOT `omega`, which would leak `propext`); `natElimMulFaithful` is structural recursion on
`n` composing ι-steps, `StepStar.appArgument`, `mulStepFires`, and `natElimAddFaithful`, with the host arithmetic
closing by `Nat.mul_succ` + the `natNumeralAt_zero_eq_natNumeralCell` bridge.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The scope-polymorphic copy step (`copyNatStep` is scope-0 only; under `mulNatStep`'s binders it lives at
scope 2).  Matches `copyNatStep` at scope 0 by `Fin`-bound proof-irrelevance. -/
def copyNatStepAt {scope : Nat} : RawTerm scope :=
  lamCell natZeroCell (lamCell natZeroCell (natSuccCell (variableCell (⟨0, Nat.succ_pos _⟩ : Fin (scope + 2)))))

/-- At scope 0 the scope-general copy step is the existing `copyNatStep`. -/
theorem copyNatStepAt_zero : (copyNatStepAt (scope := 0)) = copyNatStep := rfl

/-- The multiplication step `λ_.λr.natElim(numeralM, r, copyStep)` — folds "add `m`" onto the accumulator `r`. -/
def mulNatStep (m : Nat) : RawTerm 0 :=
  lamCell natZeroCell
    (lamCell natZeroCell (natElimCell (natNumeralAt m) (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 2)) copyNatStepAt))

/-- **The multiplication step's two β-reductions** land the inner adder `natElim(natNumeralAt m, rec, copyStep)`
with the embedded numeral fixed by `natNumeralAt_subst`.  Each `Step.beta` produces the raw `subst0 body arg`;
`firstEq`/`secondEq` rewrite it to the target (the symbolic numeral does not compute by `rfl`, so the pretty
reduct cannot be asserted directly — this is the crack-consuming recipe). -/
theorem mulStepFires (m : Nat) (pred rec : RawTerm 0) :
    StepStar (appCell (appCell (mulNatStep m) pred) rec)
      (natElimCell (natNumeralAt m) rec copyNatStepAt) := by
  have firstBeta :
      Step (appCell (mulNatStep m) pred)
        (RawTerm.subst0
          (lamCell natZeroCell
            (natElimCell (natNumeralAt m) (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 2)) copyNatStepAt)) pred) :=
    Step.beta
  have firstEq :
      RawTerm.subst0
          (lamCell natZeroCell
            (natElimCell (natNumeralAt m) (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 2)) copyNatStepAt)) pred
        = lamCell natZeroCell
            (natElimCell (natNumeralAt m) (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) copyNatStepAt) := by
    show lamCell natZeroCell
        (natElimCell (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton pred)) (natNumeralAt m))
        (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) copyNatStepAt)
      = lamCell natZeroCell
          (natElimCell (natNumeralAt m) (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) copyNatStepAt)
    rw [natNumeralAt_subst]
  have secondBeta :
      Step (appCell (lamCell natZeroCell
          (natElimCell (natNumeralAt m) (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) copyNatStepAt)) rec)
        (RawTerm.subst0 (natElimCell (natNumeralAt m) (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) copyNatStepAt) rec) :=
    Step.beta
  have secondEq :
      RawTerm.subst0 (natElimCell (natNumeralAt m) (variableCell (⟨0, Nat.succ_pos _⟩ : Fin 1)) copyNatStepAt) rec
        = natElimCell (natNumeralAt m) rec copyNatStepAt := by
    show natElimCell (RawTerm.subst (RawTermSubst.singleton rec) (natNumeralAt m)) rec copyNatStepAt
      = natElimCell (natNumeralAt m) rec copyNatStepAt
    rw [natNumeralAt_subst]
  exact StepStar.trans_compose
    (StepStar.appFunction (StepStar.single (firstEq ▸ firstBeta)))
    (StepStar.single (secondEq ▸ secondBeta))

/-- **★ The native `gen_natElim` recursor computes host `Nat.mul` faithfully.**  `natElim(rawNat n, natZero,
mulStep m) ↝* rawNat (m * n)` for ALL `m n : Nat` — the de Bruijn primitive recursor, folding "add `m`" `n`
times from `0`, reduces to the numeral of the host PRODUCT.  Induction on `n` reusing `natElimAddFaithful` as the
per-step adder; the arithmetic `m·n + m = m·(n+1)` is definitional (`Nat.mul_succ`). -/
theorem natElimMulFaithful (m : Nat) : ∀ n,
    StepStar (natElimCell (natNumeralAt n) natZeroCell (mulNatStep m)) (natNumeralAt (m * n))
  | 0 => StepStar.single Step.iotaNatElimZero
  | n + 1 => by
      have iota :
          StepStar (natElimCell (natNumeralAt (n + 1)) natZeroCell (mulNatStep m))
            (appCell (appCell (mulNatStep m) (natNumeralAt n))
              (natElimCell (natNumeralAt n) natZeroCell (mulNatStep m))) :=
        StepStar.single Step.iotaNatElimSucc
      have congArm :
          StepStar
            (appCell (appCell (mulNatStep m) (natNumeralAt n))
              (natElimCell (natNumeralAt n) natZeroCell (mulNatStep m)))
            (appCell (appCell (mulNatStep m) (natNumeralAt n)) (natNumeralAt (m * n))) :=
        StepStar.appArgument (appCell (mulNatStep m) (natNumeralAt n)) (natElimMulFaithful m n)
      have stepFire :
          StepStar (appCell (appCell (mulNatStep m) (natNumeralAt n)) (natNumeralAt (m * n)))
            (natElimCell (natNumeralAt m) (natNumeralAt (m * n)) copyNatStepAt) :=
        mulStepFires m (natNumeralAt n) (natNumeralAt (m * n))
      have adderEq :
          natElimCell (natNumeralAt m) (natNumeralAt (m * n)) copyNatStepAt
            = natElimCell (natNumeralCell m) (natNumeralCell (m * n)) copyNatStep := by
        rw [natNumeralAt_zero_eq_natNumeralCell, natNumeralAt_zero_eq_natNumeralCell, copyNatStepAt_zero]
      have adder :
          StepStar (natElimCell (natNumeralCell m) (natNumeralCell (m * n)) copyNatStep)
            (natNumeralCell (m * n + m)) :=
        natElimAddFaithful (m * n) m
      have targetEq : natNumeralCell (m * n + m) = natNumeralAt (m * (n + 1)) := by
        rw [Nat.mul_succ]; exact (natNumeralAt_zero_eq_natNumeralCell (m * n + m)).symm
      exact StepStar.trans_compose iota
        (StepStar.trans_compose congArm
          (StepStar.trans_compose stepFire
            (adderEq ▸ (targetEq ▸ adder))))

/-- Fully-concrete faithfulness smoke: `natElim(2, natZero, mulStep 3) ↝* 6` — `3 · 2` computed by the native
recursor. -/
theorem natElimMulFaithful.threeTimesTwo :
    StepStar (natElimCell (natNumeralAt 2) natZeroCell (mulNatStep 3)) (natNumeralAt 6) :=
  natElimMulFaithful 3 2

end FX1Poly.Typed
