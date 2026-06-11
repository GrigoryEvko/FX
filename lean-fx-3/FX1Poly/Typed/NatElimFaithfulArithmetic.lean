import FX1Poly.Typed.NatElimComputingCanonicity

/-! # FX1Poly/Typed/NatElimFaithfulArithmetic
    — the native `natElim` recursor computes binary addition FAITHFULLY (to the exact numeral)

`NatElimComputingCanonicity` shipped `natElimComputesToNumeral`: a closed `natElim` with a numeral zero-branch
and a value-producing successor branch computes to SOME numeral.  That is a canonicity result — it says the
fold terminates at a value — but it does NOT pin WHICH numeral, so it does not witness that the native recursor
computes a specific arithmetic function.

This file sharpens the copy fold to the exact result.  Folding the Phase-Z successor branch `natSucc (var 0)`
(which threads the recursive result, rebuilding `natSucc` once per iteration) over a numeral base computes
ADDITION:

    natElim motive (numeral base) (natSucc (var 0)) (numeral scrutinee)  ↝*  numeral (base + scrutinee)

where `+` is Lean's `Nat` addition.  So the FX native eliminator computes the SAME function as the host's
addition — numeral-faithful arithmetic on the native (non-Church) representation, the recursive-eliminator
analogue of the Church-arithmetic faithfulness results, but on `gen_natElim` directly.

## What this ships

  * **`natNumeralCell`** — the native `n`-th numeral `natSucc^n natZero` (a reusable numeral builder) with
    `natNumeralCell_isNumeral`.
  * **`natElimAddFaithful` (★)** — `natElim(m, numeral base, copyNatBranch, numeral scrutinee) ↝* numeral (base +
    scrutinee)`, by induction on `scrutinee`.  Zero: `iotaNatElimZero` projects the base (`base + 0 = base`).
    Successor: `iotaNatElimSucc` fires to the SUBSTITUTED reduct `natSucc (natElim m base copyNatBranch k)`
    (no β-step — the Phase-Z succ-iota substitutes the recursive call into `var 0` directly), the IH reduces the
    inner `natElim` to `numeral (base + k)`, and `StepStar.natSuccArgument` lifts it through the `natSucc`,
    landing `numeral (base + (k+1))` (`Nat.add_succ`).
  * **`natElimAddFaithful.twoPlusThree`** — a fully-concrete smoke.

## Zero-axiom verification

Structural recursion on the `Nat` scrutinee composing `StepStar.single` ι-steps and the `StepStar.natSuccArgument`
congruence (no β-steps — the Phase-Z succ-iota substitutes directly); the arithmetic is `Nat.add_zero` /
`Nat.add_succ`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- The native `n`-th numeral: `natSucc^n natZero`.  A reusable builder for the native (non-Church) numeral
representation. -/
def natNumeralCell : Nat → RawTerm 0
  | 0 => natZeroCell
  | n + 1 => natSuccCell (natNumeralCell n)

/-- Every native numeral satisfies `IsNatNumeral`. -/
theorem natNumeralCell_isNumeral (n : Nat) : IsNatNumeral (natNumeralCell n) := by
  induction n with
  | zero => exact IsNatNumeral.zero
  | succ k ih => exact IsNatNumeral.succ ih

/-- **★ The native `natElim` recursor computes addition, faithfully.**  Folding the Phase-Z copy successor
branch `natSucc (var 0)` over a numeral base reduces to the exact sum numeral:
`natElim(m, numeral base, copyNatBranch, numeral scrutinee) ↝* numeral (base + scrutinee)`, with `+` the host's
`Nat` addition.  The native eliminator computes the same function as Lean's addition.  A throwaway motive
`variableCell 0 : RawTerm 1` (typing-only role, discarded by both ι rules). -/
theorem natElimAddFaithful (base : Nat) : (scrutinee : Nat) →
    StepStar (natElimCell (variableCell (⟨0, by decide⟩ : Fin 1))
        (natNumeralCell base) copyNatBranch (natNumeralCell scrutinee))
      (natNumeralCell (base + scrutinee))
  | 0 => by
      -- `base + 0` is DEFINITIONALLY `base` (Nat.add recurses on the right), so no rewrite
      -- is needed (and `rw [Nat.add_zero]` would build a dependent motive over the
      -- Fin-bounded throwaway motive cell, which does not typecheck).
      show StepStar (natElimCell (variableCell (⟨0, by decide⟩ : Fin 1))
          (natNumeralCell base) copyNatBranch natZeroCell)
        (natNumeralCell base)
      exact StepStar.single Step.iotaNatElimZero
  | k + 1 => by
      -- `base + (k + 1)` is DEFINITIONALLY `(base + k) + 1`, so the target numeral is
      -- `natSuccCell (natNumeralCell (base + k))` by unfolding — no rewrite needed.
      show StepStar (natElimCell (variableCell (⟨0, by decide⟩ : Fin 1))
          (natNumeralCell base) copyNatBranch (natSuccCell (natNumeralCell k)))
        (natSuccCell (natNumeralCell (base + k)))
      have iotaStep :
          StepStar (natElimCell (variableCell (⟨0, by decide⟩ : Fin 1))
              (natNumeralCell base) copyNatBranch (natSuccCell (natNumeralCell k)))
            (natSuccCell (natElimCell (variableCell (⟨0, by decide⟩ : Fin 1))
              (natNumeralCell base) copyNatBranch (natNumeralCell k))) :=
        StepStar.single Step.iotaNatElimSucc
      have congStep :
          StepStar
            (natSuccCell (natElimCell (variableCell (⟨0, by decide⟩ : Fin 1))
              (natNumeralCell base) copyNatBranch (natNumeralCell k)))
            (natSuccCell (natNumeralCell (base + k))) :=
        StepStar.natSuccArgument (natElimAddFaithful base k)
      exact StepStar.trans_compose iotaStep congStep

/-- Fully-concrete smoke: `natElim(m, 3, copyNatBranch, 2) ↝* numeral 5` — the native recursor adds 2 and 3. -/
theorem natElimAddFaithful.twoPlusThree :
    StepStar (natElimCell (variableCell (⟨0, by decide⟩ : Fin 1))
        (natNumeralCell 3) copyNatBranch (natNumeralCell 2)) (natNumeralCell 5) :=
  natElimAddFaithful 3 2

end FX1Poly.Typed
