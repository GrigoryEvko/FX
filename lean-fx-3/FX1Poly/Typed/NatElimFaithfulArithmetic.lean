import FX1Poly.Typed.NatElimComputingCanonicity

/-! # FX1Poly/Typed/NatElimFaithfulArithmetic
    — the native `natElim` recursor computes binary addition FAITHFULLY (to the exact numeral)

`NatElimComputingCanonicity` shipped `natElimComputesToNumeral`: a closed `natElim` with a numeral zero-branch
and a value-producing successor branch computes to SOME numeral.  That is a canonicity result — it says the
fold terminates at a value — but it does NOT pin WHICH numeral, so it does not witness that the native recursor
computes a specific arithmetic function.

This file sharpens the copy fold to the exact result.  Folding the successor step `λ_. λr. natSucc r` (which
threads the recursive result, rebuilding `natSucc` once per iteration) over a numeral base computes ADDITION:

    natElim (numeral scrutinee) (numeral base) copyStep  ↝*  numeral (base + scrutinee)

where `+` is Lean's `Nat` addition.  So the FX native eliminator computes the SAME function as the host's
addition — numeral-faithful arithmetic on the native (non-Church) representation, the recursive-eliminator
analogue of the Church-arithmetic faithfulness results, but on `gen_natElim` directly.

## What this ships

  * **`natNumeralCell`** — the native `n`-th numeral `natSucc^n natZero` (a reusable numeral builder; none
    existed — the native numerals were previously built ad hoc) with `natNumeralCell_isNumeral`.
  * **`natElimAddFaithful` (★)** — `natElim(numeral scrutinee, numeral base, copyStep) ↝* numeral (base +
    scrutinee)`, by induction on `scrutinee`.  Zero: `iotaNatElimZero` projects the base (`base + 0 = base`).
    Successor: `iotaNatElimSucc` fires, the IH reduces the inner `natElim` to `numeral (base + k)`
    (`StepStar.appArgument` lifts it through the application argument), and the two `copyStep` β-steps wrap it in
    `natSucc`, landing `numeral (base + (k+1))` (`Nat.add_succ`).
  * **`natElimAddFaithful.twoPlusThree`** — a fully-concrete smoke: `natElim(2, 3, copyStep) ↝* numeral 5`.

## Zero-axiom verification

Structural recursion on the `Nat` scrutinee composing `StepStar.single` ι-steps, `StepStar.appArgument` /
`StepStar.appFunction` congruences, and two `Step.beta` contractions (with `subst0` computing definitionally on
the closed copy-step body); the arithmetic is `Nat.add_zero` / `Nat.add_succ`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
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

/-- **★ The native `natElim` recursor computes addition, faithfully.**  Folding the copy successor step
`λ_. λr. natSucc r` over a numeral base reduces to the exact sum numeral:
`natElim(numeral scrutinee, numeral base, copyStep) ↝* numeral (base + scrutinee)`, with `+` the host's `Nat`
addition.  The native eliminator computes the same function as Lean's addition. -/
theorem natElimAddFaithful (base : Nat) : (scrutinee : Nat) →
    StepStar (natElimCell (natNumeralCell scrutinee) (natNumeralCell base) copyNatStep)
      (natNumeralCell (base + scrutinee))
  | 0 => by
      show StepStar (natElimCell natZeroCell (natNumeralCell base) copyNatStep)
        (natNumeralCell (base + 0))
      rw [Nat.add_zero]
      exact StepStar.single Step.iotaNatElimZero
  | k + 1 => by
      show StepStar (natElimCell (natSuccCell (natNumeralCell k)) (natNumeralCell base) copyNatStep)
        (natNumeralCell (base + (k + 1)))
      rw [Nat.add_succ]
      have iotaStep :
          StepStar (natElimCell (natSuccCell (natNumeralCell k)) (natNumeralCell base) copyNatStep)
            (appCell (appCell copyNatStep (natNumeralCell k))
              (natElimCell (natNumeralCell k) (natNumeralCell base) copyNatStep)) :=
        StepStar.single Step.iotaNatElimSucc
      have congStep :
          StepStar
            (appCell (appCell copyNatStep (natNumeralCell k))
              (natElimCell (natNumeralCell k) (natNumeralCell base) copyNatStep))
            (appCell (appCell copyNatStep (natNumeralCell k)) (natNumeralCell (base + k))) :=
        StepStar.appArgument (appCell copyNatStep (natNumeralCell k)) (natElimAddFaithful base k)
      have firstBeta :
          Step (appCell copyNatStep (natNumeralCell k))
            (lamCell natZeroCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 1)))) :=
        Step.beta
      have secondBeta :
          Step (appCell (lamCell natZeroCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 1))))
              (natNumeralCell (base + k)))
            (natSuccCell (natNumeralCell (base + k))) :=
        Step.beta
      exact StepStar.trans_compose iotaStep
        (StepStar.trans_compose congStep
          (StepStar.trans_compose (StepStar.appFunction (StepStar.single firstBeta))
            (StepStar.single secondBeta)))

/-- Fully-concrete smoke: `natElim(2, 3, copyStep) ↝* numeral 5` — the native recursor adds 2 and 3. -/
theorem natElimAddFaithful.twoPlusThree :
    StepStar (natElimCell (natNumeralCell 2) (natNumeralCell 3) copyNatStep) (natNumeralCell 5) :=
  natElimAddFaithful 3 2

end FX1Poly.Typed
